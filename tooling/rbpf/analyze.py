"""Inspect one rBPF Compact ELF, or inventory and analyze a release."""

import argparse
from dataclasses import dataclass, field
import hashlib
import json
from pathlib import Path, PureWindowsPath
import re
import shutil
import struct
import subprocess
import sys
import tempfile
import tomllib

from analysis import Limits, analyze_program, json_file
from machine import Map, decode


CONTAINER_LIMIT = 8192
MEMBER_LIMIT = 32 * 1024 * 1024
SHA256 = re.compile(r"[a-f0-9]{64}")
INDEX_SCHEMA = "libbpf-mcu.program-index.v3"
INSPECTOR = Path(__file__).resolve().parents[1] / "target/debug/classifier-rbpf-inspect"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def valid_program_name(name):
    return (name.casefold() not in {"", ".", "..", ".ninja", "index.toml"}
            and not PureWindowsPath(name).drive
            and not any(c in "/\\" or ord(c) < 32 or ord(c) == 127 for c in name))


@dataclass(frozen=True)
class Program:
    name: str
    digest: str
    image_digest: str
    maps: tuple
    instructions: dict
    inspector: dict = field(default_factory=dict)

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


class Archive:
    def __init__(self, path, seven_zip):
        self.path = path
        self.seven_zip = seven_zip
        self.entries = {}
        listing = self.run("l", "-slt", "-ba", "--", path).decode("utf-8")
        for record in listing.strip().split("\n\n"):
            item = dict(line.split(" = ", 1) for line in record.splitlines() if " = " in line)
            name = item.get("Path")
            size = item.get("Size")
            if name is None or size is None or not size.isascii() or not size.isdecimal():
                raise ValueError("unrecognized archive listing")
            if name in self.entries:
                raise ValueError(f"duplicate archive member {name!r}")
            self.entries[name] = item

    def run(self, *args):
        result = subprocess.run([self.seven_zip, *args], capture_output=True, timeout=45)
        if result.returncode:
            detail = result.stderr.decode(errors="replace").strip()
            raise ValueError(f"7-Zip failed ({result.returncode}): {detail}")
        return result.stdout

    def read(self, name, limit, expected_size=None):
        item = self.entries.get(name)
        if item is None:
            raise ValueError(f"missing indexed member {name}")
        size = int(item["Size"])
        attrs = item.get("Attributes", "")
        if (attrs.startswith("D") or len(attrs.split()) > 1 and attrs.split()[1].startswith("l")
                or item.get("Folder") == "+" or "Symbolic Link" in item or "Hard Link" in item
                or item.get("Encrypted") == "+"):
            raise ValueError(f"indexed member is not a regular unencrypted file: {name}")
        if size > limit or expected_size is not None and size != expected_size:
            raise ValueError(f"size mismatch or limit exceeded for {name}")
        # Extract only this literal member to stdout. No archive path is written
        # to disk, including unindexed files and links.
        data = self.run("x", "-spd", "-so", "--", self.path, name)
        if len(data) != size:
            raise ValueError(f"unexpected extracted size for {name}")
        return data


def member(archive, record, name, limit=MEMBER_LIMIT):
    if not isinstance(record, dict) or record.get("path") != name:
        raise ValueError(f"invalid index path, expected {name}")
    size = record.get("size_bytes")
    digest = record.get("sha256")
    if type(size) is not int or size < 0 or not isinstance(digest, str) or not SHA256.fullmatch(digest):
        raise ValueError(f"invalid size or digest record for {name}")
    data = archive.read(name, limit, size)
    if sha(data) != digest:
        raise ValueError(f"SHA-256 mismatch for {name}")
    return data


def indexed_container(archive, program):
    index_bytes = archive.read("index.toml", 64 * 1024)
    index = tomllib.loads(index_bytes.decode())
    if index.get("schema") != INDEX_SCHEMA or index.get("program") != program:
        raise ValueError("program index schema or identity mismatch")
    member(archive, index.get("source"), f"{program}.c")
    bpf = member(archive, index.get("bpf"), f"objects/{program}_bpf.o")
    if (len(bpf) < 64 or bpf[:7] != b"\x7fELF\x02\x01\x01"
            or struct.unpack_from("<HH", bpf, 16) != (1, 247)):
        raise ValueError("bpf entry is not a little-endian relocatable eBPF object")
    modes = index.get("mode", [])
    if not isinstance(modes, list) or any(not isinstance(row, dict) for row in modes):
        raise ValueError("mode must be an array of tables")
    names = [row.get("name") for row in modes]
    if any(not isinstance(name, str) or not name for name in names) or names.count("ebpf") > 1:
        raise ValueError("invalid deployment mode or duplicate ebpf mode")
    evidence = {"index_sha256": sha(index_bytes), "modes": names}
    for row in modes:
        if row["name"] == "ebpf":
            if (row.get("role") != "xpost_container" or
                    row.get("format") != "xpost-compact-elf-v0" or "object" in row):
                raise ValueError("invalid ebpf mode role, format or object")
            name = f"containers/{program}-vm-ebpf.elf"
            evidence["container_path"] = name
            return member(archive, row.get("elf"), name, CONTAINER_LIMIT), evidence
    return None, evidence


def analyze_entry(args, data, name, out, row, selection):
    program = Program.load(data, args.inspector, name)
    row["container_sha256"] = program.digest
    row["engine_selection"] = selection
    path = args.specs / f"{name}.json" if args.specs else None
    document = json.loads(path.read_text()) if path is not None and path.is_file() else {}
    if not isinstance(document, dict):
        raise ValueError("specification must be an object")
    if not document.get("cases") and not document.get("vectors"):
        row.update(status="no_spec", reason="no declared input domain or concrete vectors")
        return
    out.mkdir()
    report = analyze_program(program, document, out, args.limits, selection)
    row.update(status="analyzed", result=f"{name}/result.json",
               concrete_counts=report["concrete_counts"],
               cases={case["id"]: case["verdict"] for case in report["cases"]})


def release(args):
    digests = json.loads(args.digests.read_text())
    if not isinstance(digests, dict) or not digests:
        raise ValueError("release digest manifest must be a nonempty object")
    for filename, digest in digests.items():
        if not filename.endswith(".7z") or not valid_program_name(filename[:-3]):
            raise ValueError(f"invalid archive filename {filename!r}")
        if not isinstance(digest, str) or not re.fullmatch(r"sha256:[a-f0-9]{64}", digest):
            raise ValueError(f"invalid SHA-256 digest for {filename}")
    seven_zip = shutil.which(args.seven_zip)
    if seven_zip is None:
        raise ValueError("7-Zip executable not found")
    version = subprocess.check_output([seven_zip, "i"], timeout=15, text=True).strip().splitlines()[0]
    args.out.mkdir(parents=True)
    rows = []
    for filename, digest in sorted(digests.items()):
        name = filename[:-3]
        path = args.assets / filename
        row = {"program": name, "asset": filename, "expected_digest": digest}
        rows.append(row)
        if not path.is_file():
            row.update(status="missing_asset", reason="expected archive is absent")
            continue
        try:
            with tempfile.TemporaryDirectory(prefix="classifier-release-") as temp:
                verified = Path(temp) / "asset.7z"
                shutil.copyfile(path, verified)
                with verified.open("rb") as stream:
                    actual = "sha256:" + hashlib.file_digest(stream, "sha256").hexdigest()
                row["asset_digest"] = actual
                if actual != digest:
                    raise ValueError("archive SHA-256 mismatch")
                data, evidence = indexed_container(Archive(verified, seven_zip), name)
                row.update(evidence)
            if data is None:
                row.update(status="missing_rbpf_container", reason="index has no ebpf mode")
            else:
                analyze_entry(args, data, name, args.out / name, row, "index.toml mode=ebpf")
        except (OSError, ValueError, TypeError, KeyError, subprocess.SubprocessError) as err:
            row.update(status="error", reason=str(err))
    unexpected = sorted(path.name for path in args.assets.glob("*.7z") if path.name not in digests)
    save_batch(args, "release", rows, tag=args.tag, seven_zip=version, unexpected_assets=unexpected)


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
            analyze_entry(args, load_bytes(path), name, args.out / name, row, "offline ebpf.elf")
        except (OSError, ValueError, TypeError, KeyError, subprocess.SubprocessError) as err:
            row.update(status="error", reason=str(err))
    save_batch(args, "offline", rows)


def save_batch(args, kind, rows, **details):
    counts = {status: sum(row["status"] == status for row in rows)
              for status in sorted({row["status"] for row in rows})}
    json_file(args.out / "summary.json", {"kind": kind, "counts": counts, "programs": rows, **details})
    print(json.dumps({"kind": kind, "counts": counts, "report": str(args.out / "summary.json")}))


def load_bytes(path):
    with path.open("rb") as stream:
        return stream.read(CONTAINER_LIMIT + 1)


def single(args):
    program = Program.load(load_bytes(args.container), args.inspector)
    spec = json.loads(args.spec.read_text())
    args.out.mkdir(parents=True)
    report = analyze_program(program, spec, args.out, args.limits, "explicit --engine ebpf")
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
    batch = commands.add_parser("release", parents=[common])
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
