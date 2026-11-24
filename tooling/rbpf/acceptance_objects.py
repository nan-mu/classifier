"""Check the v0.1.1 object release and replay its witnesses through the CLI."""

import argparse
import io
import json
from pathlib import Path
import shutil
import struct
import subprocess

from elftools.elf.elffile import ELFFile

from acceptance import NETWORK, NEGATIVES, cli, read, require, verify_smt
from analysis import json_file
from analyze import Archive, MEMBER_LIMIT, indexed_object, sha
from make_specs import EXB2


def verify_release(report_dir, evidence, specs):
    report = read(report_dir / "summary.json")
    rows = {row["program"]: row for row in report["programs"]}
    require(set(rows) == set(EXB2 + NETWORK) and report["tag"] == "v0.1.1",
            "unexpected v0.1.1 inventory")
    require(not report["unexpected_assets"] and len(report["programs"]) == 12,
            "expected the 12 original assets")
    total = 0
    for name, row in rows.items():
        require(row["status"] == "analyzed", f"{name}: {row}")
        result = read(report_dir / row["result"])
        require(result["backend"] == "angr/Heimdall" and result["section"] == "xdp"
                and result["object_sha256"] == row["object_sha256"]
                and row["bpf_path"] == f"objects/{name}_bpf.o",
                f"{name}: expected an analyzed release XDP object")
        paths = sorted((evidence / "vectors" / name).glob("*/expected.json"))
        expected = sorted((path.parent.name, "holds") for path in paths)
        actual = sorted((vector["id"], vector["verdict"]) for vector in result["vectors"])
        require(expected == actual and result["concrete_counts"] ==
                {"passed": len(paths), "total": len(paths)}, f"{name}: vectors {actual}")
        total += len(paths)

        cases = {case["id"]: "holds" for case in read(specs / f"{name}.json")["cases"]}
        if name in NEGATIVES:
            cases[NEGATIVES[name]] = "counterexample"
        require(row["cases"] == cases, f"{name}: {row['cases']}")
    require(total == 23, f"expected 23 original vectors, got {total}")
    return rows


def release_input(name, args, rows, out):
    filename = name + ".7z"
    path = args.assets / filename
    require("sha256:" + sha(path.read_bytes()) == rows[name]["asset_digest"],
            f"{filename} differs from the formally analyzed asset")
    archive = Archive(path, args.seven_zip)
    data, index, _ = indexed_object(archive, name)
    require(sha(data) == rows[name]["object_sha256"], f"{name}: object hash changed")
    output = out / f"{name}_bpf.o"
    output.write_bytes(data)
    return output, archive, index


def single(obj, spec, out, *options):
    return cli("analyze-object", obj, "--spec", spec, "--out", out, *options,
               capture_output=True, text=True)


def expect_load_error(data, pattern, args, out, name):
    path = out / f"{name}.o"
    path.write_bytes(data)
    try:
        single(path, args.specs / "just_drop.json", out / name)
    except subprocess.CalledProcessError as err:
        require(err.returncode == 1 and pattern in err.stderr, f"{name}: {err.stderr}")
        (out / f"{name}.log").write_text(err.stderr)
    else:
        raise RuntimeError(f"{name}: wrong object accepted")


def object_only_archive(args, out, artifact, archive, index):
    assets = out / "object-only-fixture"
    assets.mkdir()
    staging = assets / "just_drop"
    staging.mkdir()
    for field in ("source", "bpf"):
        path = index[field]["path"]
        target = staging / path
        target.parent.mkdir(parents=True, exist_ok=True)
        value = artifact.read_bytes() if field == "bpf" else archive.read(path, MEMBER_LIMIT)
        target.write_bytes(value)
    # The original v3 index is preserved up to the deployment mode tables.
    raw = archive.read("index.toml", 64 * 1024).decode()
    (staging / "index.toml").write_text(raw.split("[[mode]]", 1)[0])
    sample = assets / "just_drop.7z"
    subprocess.run([args.seven_zip, "a", "-bd", sample, "index.toml",
                    index["source"]["path"], index["bpf"]["path"]],
                   cwd=staging, stdout=subprocess.DEVNULL, check=True)
    digests = assets / "digests.json"
    json_file(digests, {sample.name: "sha256:" + sha(sample.read_bytes())})
    target = out / "object-only-release"
    cli("release", "--tag", "v0.1.1", "--assets", assets, "--digests", digests,
        "--specs", args.specs, "--seven-zip", args.seven_zip, "--out", target)
    row, = read(target / "summary.json")["programs"]
    require(row["status"] == "analyzed" and row["concrete_counts"] == {"passed": 1, "total": 1}
            and read(target / row["result"])["backend"] == "angr/Heimdall",
            f"object-only release: {row}")

    json_file(digests, {sample.name: "sha256:" + "0" * 64})
    target = out / "wrong-asset-digest"
    cli("release", "--tag", "v0.1.1", "--assets", assets, "--digests", digests,
        "--specs", args.specs, "--seven-zip", args.seven_zip, "--out", target)
    row, = read(target / "summary.json")["programs"]
    require(row["status"] == "error" and "archive SHA-256 mismatch" in row["reason"],
            f"wrong release digest: {row}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--release-results", required=True, type=Path)
    parser.add_argument("--assets", required=True, type=Path)
    parser.add_argument("--evidence", required=True, type=Path)
    parser.add_argument("--specs", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--seven-zip", default="7z")
    parser.add_argument("--z3", help="also resolve saved SMT-LIB with this executable")
    args = parser.parse_args()
    args.seven_zip = shutil.which(args.seven_zip)
    require(args.seven_zip, "7-Zip executable not found")
    out = args.out.resolve()
    out.mkdir(parents=True)
    rows = verify_release(args.release_results, args.evidence, args.specs)

    for name, negative in NEGATIVES.items():
        obj, _, _ = release_input(name, args, rows, out)
        directory = args.release_results / name / "cases" / negative
        witness = read(directory / "result.json")["counterexample"]
        require(witness["replayed"], f"{name}: counterexample failed internal replay")
        target = "blacklist[c0000211].value" if name == "firewall" else "packet[77]"
        require([diff["field"] for diff in witness["differences"]] == [f"0: {target}"],
                f"{name}: unexpected counterexample observation")
        replay = out / f"replay-{name}"
        single(obj, directory / "counterexample.json", replay)
        result = read(replay / "cases" / negative / "result.json")
        require(result["counterexample"]["differences"] == witness["differences"],
                f"{name}: external replay changed observations")
        if name == "firewall":
            data = bytearray(obj.read_bytes())
            elf = ELFFile(io.BytesIO(data))
            section = elf.get_section_by_name(".relxdp")
            struct.pack_into("<I", data, section["sh_offset"] + 12, 0)
            expect_load_error(data, ".relxdp+0x60: symbol", args, out, "unbound-map")

    copy, _, _ = release_input("copy", args, rows, out)
    single(copy, args.specs / "copy.json", out / "budget-copy", "--max-back-edges", "0")
    budget = read(out / "budget-copy/vectors/valid/result.json")
    require(budget["verdict"] == "undetermined" and budget["coverage"]["status"] == "sat"
            and [gap["kind"] for gap in budget["unresolved"]] == ["loop_budget"],
            f"copy: expected a loop budget coverage gap, got {budget['verdict']}")

    drop, archive, index = release_input("just_drop", args, rows, out)
    object_only_archive(args, out, drop, archive, index)
    payload = bytearray(drop.read_bytes())
    elf = ELFFile(io.BytesIO(payload))
    offset = elf.get_section_by_name("xdp")["sh_offset"]
    # Use the actual MOV64 shape from the brief in the otherwise valid ELF.
    payload[offset:offset + 8] = bytes.fromhex("b700000001000000")
    legal = out / "legal-mov.o"
    legal.write_bytes(payload)
    single(legal, args.specs / "just_drop.json", out / "legal-mov")
    legal_result = read(out / "legal-mov/result.json")
    require(legal_result["concrete_counts"] == {"passed": 1, "total": 1},
            "legal MOV did not yield DROP")
    payload[offset + 2] = 7
    expect_load_error(payload, "slot 0: invalid or unsupported ALU encoding (0xb7)",
                      args, out, "reserved-mov-field")
    expect_load_error(b"\x7fELF", "invalid eBPF ELF object", args, out, "truncated-object")

    receipt = {"release": "v0.1.1", "programs": 12, "concrete_vectors": 23,
               "counterexample_replays": len(NEGATIVES), "loop_budget": budget["coverage"]}
    if args.z3:
        receipt["query_replay"] = {"release": verify_smt(args.release_results, args.z3),
                                   "diagnostics": verify_smt(out, args.z3)}
    json_file(out / "acceptance.json", receipt)
    print(json.dumps(receipt, ensure_ascii=False))


if __name__ == "__main__":
    main()
