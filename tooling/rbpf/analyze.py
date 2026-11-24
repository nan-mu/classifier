"""Analyze historical Compact ELF containers."""

import argparse
from dataclasses import dataclass, field
import hashlib
import json
from pathlib import Path
import subprocess

from analysis import Limits, analyze_program
from machine import Machine, Map, decode
from release_input import (
    Archive, MEMBER_LIMIT, analyze_entry, indexed_object, member, run_release, save_batch, sha,
)


CONTAINER_LIMIT = 8192
INSPECTOR = Path(__file__).resolve().parents[1] / "target/debug/classifier-rbpf-inspect"


@dataclass(frozen=True)
class Program:
    name: str
    digest: str
    image_digest: str
    maps: tuple
    instructions: dict
    inspector: dict = field(default_factory=dict)
    backend_name = "Python/Z3"
    versions = {}

    @property
    def artifact(self):
        return {"container_sha256": self.digest}

    def execute(self, domain, limits):
        machine = Machine(self.instructions, self.maps, limits.max_steps, limits.max_back_edges,
                          limits.max_paths, limits.timeout_ms)
        return machine.run(domain.initial())

    @classmethod
    def load(cls, data, inspector, expected=None):
        if len(data) > CONTAINER_LIMIT:
            raise ValueError("Compact ELF exceeds 8192 bytes")
        result = subprocess.run([inspector], input=data, capture_output=True, timeout=15)
        if result.returncode:
            raise ValueError(result.stderr.decode(errors="replace").strip())
        info = json.loads(result.stdout)
        if expected is not None and info["name"] != expected:
            raise ValueError(f"container program is {info['name']!r}, expected {expected!r}")
        maps = tuple(Map(**entry) for entry in info["maps"])
        image = bytes(info["image"])
        with inspector.open("rb") as binary:
            build = {"version": info["inspector_version"],
                     "sha256": hashlib.file_digest(binary, "sha256").hexdigest()}
        return cls(info["name"], sha(data), sha(image), maps, decode(image, len(maps)), build)

def indexed_container(archive, program):
    _, index, evidence = indexed_object(archive, program)
    modes = index.get("mode", [])
    if not isinstance(modes, list) or any(not isinstance(row, dict) for row in modes):
        raise ValueError("mode must be an array of tables")
    names = [row.get("name") for row in modes]
    if any(not isinstance(name, str) or not name for name in names) or names.count("ebpf") > 1:
        raise ValueError("invalid deployment mode or duplicate ebpf mode")
    evidence["modes"] = names
    for row in modes:
        if row["name"] == "ebpf":
            if (row.get("role") != "xpost_container" or
                    row.get("format") != "xpost-compact-elf-v0" or "object" in row):
                raise ValueError("invalid ebpf mode role, format or object")
            name = f"containers/{program}-vm-ebpf.elf"
            evidence["container_path"] = name
            return member(archive, row.get("elf"), name, CONTAINER_LIMIT), evidence
    return None, evidence


def release(args):
    run_release(args, indexed_container, lambda data, name: Program.load(data, args.inspector, name),
                "index.toml mode=ebpf", "container")


def offline(args):
    paths = sorted(args.containers.glob("*/ebpf.elf"))
    if not paths:
        raise ValueError(f"no offline rBPF containers under {args.containers}")
    args.out.mkdir(parents=True)
    rows = []
    for path in paths:
        name = path.parent.name
        row = {"program": name, "container_path": str(path)}
        rows.append(row)
        try:
            program = Program.load(load_bytes(path), args.inspector, name)
            analyze_entry(args, program, name, args.out / name, row, "offline ebpf.elf")
        except (OSError, ValueError, TypeError, KeyError, subprocess.SubprocessError) as err:
            row.update(status="error", reason=str(err))
    save_batch(args, "offline", rows)


def load_bytes(path):
    with path.open("rb") as stream:
        return stream.read(CONTAINER_LIMIT + 1)


def single(args):
    program = Program.load(load_bytes(args.container), args.inspector)
    selection = "explicit --engine ebpf"
    spec = json.loads(args.spec.read_text())
    args.out.mkdir(parents=True)
    report = analyze_program(program, spec, args.out, args.limits, selection)
    print(json.dumps({"program": program.name, "concrete_counts": report["concrete_counts"],
                      "cases": {case["id"]: case["verdict"] for case in report["cases"]}}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("--inspector", type=Path, default=INSPECTOR)
    common.add_argument("--out", type=Path, required=True, help="new evidence directory")
    common.add_argument("--max-steps", type=int, default=2_000_000)
    common.add_argument("--max-back-edges", type=int, default=100_000)
    common.add_argument("--max-paths", type=int, default=256)
    common.add_argument("--timeout-ms", type=int, default=5000, help="per solver query")
    commands = parser.add_subparsers(dest="command", required=True)
    one = commands.add_parser("analyze", parents=[common])
    one.add_argument("container", type=Path)
    one.add_argument("--engine", required=True, choices=["ebpf"])
    one.add_argument("--spec", type=Path, required=True)
    one.set_defaults(run=single)
    batch = commands.add_parser("container-release", parents=[common])
    batch.add_argument("--tag", required=True)
    batch.add_argument("--assets", type=Path, required=True)
    batch.add_argument("--digests", type=Path, required=True)
    batch.add_argument("--specs", type=Path)
    batch.add_argument("--seven-zip", default="7z")
    batch.set_defaults(run=release)
    comparison = commands.add_parser("offline", parents=[common])
    comparison.add_argument("--containers", type=Path, required=True)
    comparison.add_argument("--specs", type=Path, required=True)
    comparison.set_defaults(run=offline)
    args = parser.parse_args()
    args.inspector = args.inspector.resolve()
    if min(args.max_steps, args.max_paths, args.timeout_ms) < 1 or args.max_back_edges < 0:
        parser.error("limits must be positive (max-back-edges may be zero)")
    args.limits = Limits(args.max_steps, args.max_back_edges, args.max_paths, args.timeout_ms)
    try:
        args.run(args)
    except (OSError, ValueError, TypeError, KeyError, subprocess.SubprocessError) as err:
        parser.exit(1, f"error: {err}\n")


if __name__ == "__main__":
    main()
