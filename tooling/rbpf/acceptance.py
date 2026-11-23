"""Run and check the v0.1.0 release and offline evidence through the CLI."""

import argparse
import json
from pathlib import Path
import shutil
import struct
import subprocess
import sys
import tempfile

from analysis import json_file
from analyze import Archive, MEMBER_LIMIT, sha
from make_specs import EXB2


HERE = Path(__file__).resolve().parent
NETWORK = ("case_mark", "case_swap", "firewall", "just_drop", "just_tx")
NEGATIVES = {"case_mark": "wrong-version", "case_swap": "wrong-version", "firewall": "wrong-count"}


def read(path):
    return json.loads(path.read_text())


def require(condition, detail):
    if not condition:
        raise RuntimeError(detail)


def cli(*args, **kwargs):
    return subprocess.run([sys.executable, HERE / "analyze.py", *args], check=True, **kwargs)


def inventory(assets, digests, out, specs=None):
    command = ["release", "--tag", "v0.1.0", "--assets", assets, "--digests", digests, "--out", out]
    if specs is not None:
        command.extend(["--specs", specs])
    cli(*command)
    return read(out / "summary.json")


def partial_release(assets, containers, specs, out):
    work = out / "partial-fixtures"
    work.mkdir()
    seven_zip = shutil.which("7z")
    require(seven_zip, "7-Zip is required for the partial release fixture")
    digests = {"case_swap.7z": "sha256:" + "0" * 64}
    expected = {"case_swap": "missing_asset"}
    for program, shape in (("case_mark", "bad_digest"), ("copy", "bad_image"),
                           ("just_drop", "object"), ("just_tx", "valid")):
        asset = f"{program}.7z"
        original = Archive(assets / asset, seven_zip)
        with tempfile.TemporaryDirectory(prefix="classifier-release-fixture-") as temp:
            staging = Path(temp)
            index = original.read("index.toml", 64 * 1024)
            source, bpf = f"{program}.c", f"objects/{program}_bpf.o"
            for name in (source, bpf):
                target = staging / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(original.read(name, MEMBER_LIMIT))
            data = (containers / program / "ebpf.elf").read_bytes()
            if shape == "bad_digest":
                data = data[:-1] + bytes([data[-1] ^ 1])
            if shape == "bad_image":
                image_offset, image_size = struct.unpack_from("<II", data, 52 + 2 * 40 + 16)
                invalid = bytearray(data)
                invalid[image_offset] = 0
                invalid[-32:] = bytes.fromhex(sha(invalid[image_offset:image_offset + image_size]))
                data = bytes(invalid)
            if shape == "object":
                data = (staging / bpf).read_bytes()
            relative = f"containers/{program}-vm-ebpf.elf"
            target = staging / relative
            target.parent.mkdir()
            target.write_bytes(data)
            row = (f'\n[[mode]]\nname = "ebpf"\nrole = "xpost_container"\n'
                   f'format = "xpost-compact-elf-v0"\n'
                   f'elf = {{ path = "{relative}", size_bytes = {len(data)}, sha256 = "{sha(data)}" }}\n')
            (staging / "index.toml").write_bytes(index + row.encode())
            subprocess.run([seven_zip, "a", "-bd", work / asset, "index.toml", source, bpf, relative],
                           cwd=staging, stdout=subprocess.DEVNULL, check=True)
        digests[asset] = "sha256:" + sha((work / asset).read_bytes())
        expected[program] = "analyzed" if shape == "valid" else "error"
    shutil.copyfile(assets / "firewall.7z", work / "firewall.7z")
    digests["firewall.7z"] = "sha256:" + "0" * 64
    expected["firewall"] = "error"
    json_file(work / "digests.json", digests)
    report = inventory(work, work / "digests.json", out / "partial-release", specs)
    rows = {row["program"]: row for row in report["programs"]}
    require({name: row["status"] for name, row in rows.items()} == expected,
            f"unexpected partial release status: {rows}")
    for name in ("case_mark", "just_drop"):
        require("Compact ELF" in rows[name]["reason"], f"{name} must fail Compact ELF validation")
    require("invalid rBPF instruction" in rows["copy"]["reason"], "malformed rBPF image accepted")
    require(rows["firewall"]["reason"] == "archive SHA-256 mismatch", "wrong asset digest accepted")
    require(rows["just_tx"]["concrete_counts"] == {"passed": 2, "total": 2},
            "indexed just_tx did not replay both vectors")


def verify_offline(containers, specs, out):
    offline = out / "offline"
    cli("offline", "--containers", containers, "--specs", specs, "--out", offline)
    report = read(offline / "summary.json")
    statuses = {row["program"]: row["status"] for row in report["programs"]}
    require(statuses == dict.fromkeys(EXB2 + NETWORK, "analyzed"), f"offline inventory: {statuses}")
    vector_count = 0
    for row in report["programs"]:
        passed, total = (row["concrete_counts"][key] for key in ("passed", "total"))
        require(passed == total and total > 0, f"failed concrete vector: {row}")
        vector_count += total
        name = row["program"]
        expected = {case["id"]: "holds" for case in read(specs / f"{name}.json")["cases"]}
        if negative := NEGATIVES.get(name):
            expected[negative] = "counterexample"
        require(row["cases"] == expected, f"unexpected case verdicts: {row}")
    require(vector_count == 23, f"expected 23 vectors, got {vector_count}")

    for name, negative in NEGATIVES.items():
        evidence = offline / name / "cases" / negative
        report = read(evidence / "result.json")
        witness = report["counterexample"]
        require(witness["replayed"], f"{name}: counterexample failed internal replay")
        target = ("blacklist[c0000211].value" if name == "firewall" else "packet[77]")
        require([diff["field"] for diff in witness["differences"]] == [f"0: {target}"],
                f"{name}: wrong counterexample observation")
        replay = out / f"replay-{name}"
        cli("analyze", containers / name / "ebpf.elf", "--engine", "ebpf",
            "--spec", evidence / "counterexample.json", "--out", replay)
        replayed = read(replay / "cases" / negative / "result.json")
        require(replayed["counterexample"]["differences"] == witness["differences"],
                f"{name}: counterexample CLI replay changed observations")

    for name in EXB2:
        path = out / f"{name}-loop.json"
        document = read(specs / f"{name}.json")
        json_file(path, {"cases": [row for row in document["cases"] if row["id"] == "magic-byte"]})
        run = out / f"budget-{name}"
        cli("analyze", containers / name / "ebpf.elf", "--engine", "ebpf",
            "--spec", path, "--max-back-edges", "0", "--out", run)
        report = read(run / "cases/magic-byte/result.json")
        require(report["verdict"] == "undetermined" and report["coverage"]["status"] == "sat",
                f"{name}: loop budget must leave uncovered input")
        require([gap["kind"] for gap in report["unresolved"]] == ["loop_budget"]
                and report["uncovered_input"]["packet_hex"].startswith("45"),
                f"{name}: loop budget lost the valid-magic input")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bundle", type=Path, required=True, help="extracted taskbook ZIP")
    parser.add_argument("--upstream", type=Path, required=True, help="pinned libbpf-mcu checkout")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    bundle = args.bundle.resolve()
    evidence, assets = bundle / "evidence", bundle / "release/v0.1.0"
    out = args.out.resolve()
    out.mkdir(parents=True)
    report = inventory(assets, evidence / "digests.json", out / "release")
    expected = dict.fromkeys(EXB2 + NETWORK, "missing_rbpf_container")
    require({row["program"]: row["status"] for row in report["programs"]} == expected
            and not report["unexpected_assets"], "unexpected v0.1.0 release inventory")
    specs = out / "specs"
    subprocess.run([sys.executable, HERE / "make_specs.py", "--evidence", evidence,
                    "--upstream", args.upstream, "--out", specs], check=True)
    containers = evidence / "containers"
    partial_release(assets, containers, specs, out)
    verify_offline(containers, specs, out)
    print("Acceptance passed: 12 release assets, 12 offline programs, 23 vectors, "
          "3 counterexample replays, 7 loop-budget checks.")


if __name__ == "__main__":
    main()
