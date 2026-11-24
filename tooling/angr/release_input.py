"""Read and validate the published program archives and their indexes."""

import hashlib
import json
from pathlib import Path, PureWindowsPath
import re
import shutil
import struct
import subprocess
import tempfile
import tomllib

from proof import analyze_program, json_file


MEMBER_LIMIT = 32 * 1024 * 1024
SHA256 = re.compile(r"[a-f0-9]{64}")
INDEX_SCHEMA = "libbpf-mcu.program-index.v3"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def valid_program_name(name):
    return (name.casefold() not in {"", ".", "..", ".ninja", "index.toml"}
            and not PureWindowsPath(name).drive
            and not any(c in "/\\" or ord(c) < 32 or ord(c) == 127 for c in name))


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


def indexed_object(archive, program):
    index_bytes = archive.read("index.toml", 64 * 1024)
    index = tomllib.loads(index_bytes.decode())
    if index.get("schema") != INDEX_SCHEMA or index.get("program") != program:
        raise ValueError("program index schema or identity mismatch")
    member(archive, index.get("source"), f"{program}.c")
    bpf = member(archive, index.get("bpf"), f"objects/{program}_bpf.o")
    if (len(bpf) < 64 or bpf[:7] != b"\x7fELF\x02\x01\x01"
            or struct.unpack_from("<HH", bpf, 16) != (1, 247)):
        raise ValueError("bpf entry is not a little-endian relocatable eBPF object")
    return bpf, index, {"index_sha256": sha(index_bytes), "bpf_path": index["bpf"]["path"]}


def analyze_entry(args, program, name, out, row, selection):
    row.update(program.artifact)
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


def run_release(args, index_reader, load, selection, artifact_kind):
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
                row["stage"] = "index"
                archive = Archive(verified, seven_zip)
                data, evidence = index_reader(archive, name)
                row.update(evidence)
            if data is None:
                row.update(status="missing_rbpf_container", reason="index has no ebpf mode")
            else:
                row["stage"] = artifact_kind
                program = load(data, name)
                row["stage"] = "specification or analysis"
                analyze_entry(args, program, name, args.out / name, row, selection)
        except (OSError, ValueError, TypeError, KeyError, subprocess.SubprocessError) as err:
            row.update(status="error", reason=str(err))
        else:
            row.pop("stage", None)
    unexpected = sorted(path.name for path in args.assets.glob("*.7z") if path.name not in digests)
    save_batch(args, "release", rows, tag=args.tag, seven_zip=version, unexpected_assets=unexpected)


def save_batch(args, kind, rows, **details):
    counts = {status: sum(row["status"] == status for row in rows)
              for status in sorted({row["status"] for row in rows})}
    json_file(args.out / "summary.json", {"kind": kind, "counts": counts, "programs": rows, **details})
    print(json.dumps({"kind": kind, "counts": counts, "report": str(args.out / "summary.json")}))
