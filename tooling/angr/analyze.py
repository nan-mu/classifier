"""Analyze a libbpf-mcu XDP object or its verified release archives."""

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
import subprocess

from angr_backend import AngrBackend
from elf_object import load_xdp
from proof import Limits, analyze_program
from release_input import MEMBER_LIMIT, indexed_object, run_release, sha


@dataclass(frozen=True)
class Program:
    name: str
    image_digest: str
    maps: tuple
    instructions: dict
    backend: AngrBackend
    artifact: dict

    backend_name = AngrBackend.name
    versions = AngrBackend.versions
    inspector = {}

    @classmethod
    def load(cls, data, name):
        expected, maps, instructions, artifact, code = load_xdp(data)
        backend = AngrBackend(data, expected, maps, instructions, artifact)
        artifact.update(object_sha256=sha(data), relocated_image_sha256=sha(expected))
        return cls(name, sha(code), maps, instructions, backend, artifact)

    def execute(self, domain, limits):
        return self.backend.run(domain, self.maps, limits)

    def return_formula(self, exits):
        return self.backend.return_formula(exits)


def single(args):
    with args.object.open("rb") as stream:
        data = stream.read(MEMBER_LIMIT + 1)
    if len(data) > MEMBER_LIMIT:
        raise ValueError("eBPF object exceeds the member size limit")
    program = Program.load(data, args.object.stem.removesuffix("_bpf"))
    spec = json.loads(args.spec.read_text())
    args.out.mkdir(parents=True)
    report = analyze_program(program, spec, args.out, args.limits, "explicit eBPF object")
    print(json.dumps({"program": program.name, "concrete_counts": report["concrete_counts"],
                      "cases": {case["id"]: case["verdict"] for case in report["cases"]}}))


def release(args):
    def read_object(archive, name):
        data, _, evidence = indexed_object(archive, name)
        return data, evidence

    run_release(args, read_object, Program.load, "index.toml bpf.path", "object")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("--out", type=Path, required=True, help="new evidence directory")
    common.add_argument("--max-steps", type=int, default=2_000_000)
    common.add_argument("--max-back-edges", type=int, default=100_000)
    common.add_argument("--max-paths", type=int, default=256)
    common.add_argument("--timeout-ms", type=int, default=5000, help="per solver query")
    commands = parser.add_subparsers(dest="command", required=True)
    obj = commands.add_parser("analyze-object", parents=[common])
    obj.add_argument("object", type=Path)
    obj.add_argument("--spec", type=Path, required=True)
    obj.set_defaults(run=single)
    batch = commands.add_parser("release", parents=[common])
    batch.add_argument("--tag", required=True)
    batch.add_argument("--assets", type=Path, required=True)
    batch.add_argument("--digests", type=Path, required=True)
    batch.add_argument("--specs", type=Path)
    batch.add_argument("--seven-zip", default="7z")
    batch.set_defaults(run=release)
    args = parser.parse_args()
    if min(args.max_steps, args.max_paths, args.timeout_ms) < 1 or args.max_back_edges < 0:
        parser.error("limits must be positive (max-back-edges may be zero)")
    args.limits = Limits(args.max_steps, args.max_back_edges, args.max_paths, args.timeout_ms)
    try:
        args.run(args)
    except (OSError, ValueError, TypeError, KeyError, subprocess.SubprocessError) as err:
        parser.exit(1, f"error: {err}\n")


if __name__ == "__main__":
    main()
