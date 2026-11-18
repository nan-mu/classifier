#!/usr/bin/env python3
import argparse
import importlib.util
import hashlib
import json
import os
import tempfile
from pathlib import Path
import subprocess
import struct
import sys
sys.dont_write_bytecode = True
import tomllib


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(args):
    result = subprocess.run([str(arg) for arg in args], capture_output=True, text=True, timeout=30)
    if result.returncode:
        raise RuntimeError(f"{args}: exit {result.returncode}: {result.stderr}")
    return result.stdout


def elf_code(path, section):
    data = path.read_bytes()
    assert data[:6] == b"\x7fELF\x02\x01"
    table = struct.unpack_from("<Q", data, 40)[0]
    size, count, strings_index = struct.unpack_from("<HHH", data, 58)
    sections = [struct.unpack_from("<IIQQQQIIQQ", data, table + size * i) for i in range(count)]
    strings = sections[strings_index]
    names = data[strings[4]:strings[4] + strings[5]]
    matches = [s for s in sections if names[s[0]:].split(b"\0", 1)[0].decode() == section and s[2] & 4]
    assert len(matches) == 1
    code_section = matches[0]
    code = data[code_section[4]:code_section[4] + code_section[5]]
    return code


def elf_backedges(path, section):
    code = elf_code(path, section)
    assert len(code) % 8 == 0
    edges, count, slot = [], 0, 0
    while slot < len(code) // 8:
        opcode = code[slot * 8]
        offset = struct.unpack_from("<h", code, slot * 8 + 2)[0]
        target = slot + 1 + offset
        if opcode & 7 in (5, 6) and opcode & 0xf0 not in (0x80, 0x90) and target <= slot:
            edges.append([slot, target])
        slot += 2 if opcode == 0x18 else 1
        count += 1
    assert slot == len(code) // 8
    return count, edges


def source_roots(index, explicit):
    roots = []
    for start in [index.resolve(), Path.cwd().resolve()]:
        for root in [start, *start.parents]:
            if (root / '.git').exists() and (root / 'alive2').is_dir() and (root / 'tooling').is_dir():
                roots.append(root)
                break
    if explicit:
        roots.append(explicit.resolve())
    if not roots:
        raise ValueError("cannot discover source root; pass --source-root")
    return roots


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--compiler", type=Path, required=True)
    parser.add_argument("--loader", type=Path, required=True)
    parser.add_argument("--index", type=Path, required=True)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--source-root", type=Path)
    args = parser.parse_args()
    roots = source_roots(args.index, args.source_root)
    destination = args.out_dir.resolve()
    if any(destination == root or root in destination.parents for root in roots):
        raise ValueError("output inside source root")
    fixture_script = Path(__file__).with_name("compiler-structure.py")
    spec = importlib.util.spec_from_file_location("compiler_structure", fixture_script)
    fixture_module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(fixture_module)
    evidence_path = args.out_dir / "verification.json"
    evidence_path.unlink(missing_ok=True)
    snapshot = tomllib.loads(args.index.read_text())
    run([args.compiler, "compile-corpus", "--index", args.index, "--out-dir", args.out_dir, "--source-root", roots[0]])
    run(["python3", fixture_script, "--compiler", args.compiler, "--loader", args.loader, "--source-root", roots[0]])
    run([args.loader, "--self-test"])
    programs = []
    for program in snapshot["program"]:
        name = program["name"]
        directory = args.out_dir / name
        alive = directory / f"{name}.alive"
        origin = directory / f"{name}.origin.json"
        report_path = directory / "compile-report.toml"
        metadata = json.loads(origin.read_text())
        report = tomllib.loads(report_path.read_text())
        original = args.index.parent / program["object"]
        assert sha256(original) == program["sha256"] == metadata["elf_sha256"] == report["elf_sha256"]
        assert sha256(alive) == metadata["alive_sha256"] == report["alive_sha256"]
        assert report["status"] == program["expected_status"] == "converted"
        assert report["entry"] == program["expected_entry"]
        assert report["section"] == program["expected_section"]
        count, backedges = elf_backedges(original, program["expected_section"])
        assert count == report["instructions"] == program["expected_instructions"]
        assert backedges == program["expected_backedges"]
        assert report["loop"] == bool(backedges)
        assert report["origin_sha256"] == sha256(origin)
        assert report["implementation_proof"] == "not_proven"
        assert len(metadata["instructions"]) == report["instructions"]
        fixture_module.validate_origin(metadata, alive.read_text(), elf_code(original, program["expected_section"]))
        definitions = {line.strip().split(" = ", 1)[0] for line in alive.read_text().splitlines() if " = " in line}
        mapped = set(metadata["prologue_ir"])
        mapped.update(value for instruction in metadata["instructions"] for value in instruction["ir"])
        assert definitions == mapped, f"{name}: incomplete definition origin"
        structure = run([args.loader, "--inspect", alive])
        normalized = directory / f"{name}.normalized.alive"
        normalized.write_text(run([args.loader, "--normalize", alive]))
        assert run([args.loader, "--inspect", normalized]) == structure, f"{name}: round trip changed structure"
        origin.rename(origin.with_suffix(".unavailable"))
        try:
            assert run([args.loader, "--inspect", alive]) == structure
            origin.write_text('{"schema":"broken","alive_sha256":"wrong"}')
            assert run([args.loader, "--inspect", alive]) == structure
        finally:
            origin.unlink(missing_ok=True)
            origin.with_suffix(".unavailable").rename(origin)
        programs.append({
            "name": name,
            "input": program["object"], "elf_sha256": sha256(original),
            "alive": f"{name}/{alive.name}", "alive_sha256": sha256(alive),
            "origin": f"{name}/{origin.name}", "origin_sha256": sha256(origin),
            "report": f"{name}/{report_path.name}", "report_sha256": sha256(report_path),
            "instructions": report["instructions"], "loop": report["loop"],
            "entry": report["entry"], "section": report["section"],
            "expected_status": program["expected_status"], "actual_status": report["status"],
            "backedges": backedges, "reason": "",
            "loaded": True, "round_trip": True, "origin_independent": True,
            "implementation_proof": "not_proven", "artifact_proof": "not_proven",
            "source_view": "incomplete",
        })
    smoke = []
    for name in ["div2", "xdp_drop"]:
        alive = args.out_dir / name / f"{name}.alive"
        smoke.append({"name": name, "result": run([args.loader, "--smoke", alive]).strip()})
    loop = args.out_dir / "helper_loop" / "helper_loop.alive"
    rejected = subprocess.run([str(args.loader), "--smoke", str(loop)], capture_output=True, text=True, timeout=30)
    assert rejected.returncode != 0 and "explicit --unroll" in rejected.stderr
    smoke.append({"name": "helper_loop", "unroll": 1, "result": run([args.loader, "--smoke", loop, "--unroll", "1"]).strip()})
    evidence = {
        "evidence_kind": "test", "status": "verified_for_recorded_checks",
        "compiler_sha256": sha256(args.compiler), "loader_sha256": sha256(args.loader),
        "snapshot_sha256": sha256(args.index), "task_a_index": snapshot["task_a_index"],
        "alive2_pin": "adacbd5180ccf95075e9867c4f0c259f59c9fef2",
        "rocq_pin": "78d65a77592aae84b31f86385f8be4ab83b45ccb",
        "implementation_proof": "not_proven", "artifact_proof": "not_proven",
        "programs": programs, "smoke": smoke, "independent_structural_fixtures": len(fixture_module.FIXTURES),
    }
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", dir=args.out_dir, prefix=".verification.", delete=False) as output:
            temporary = Path(output.name)
            output.write(json.dumps(evidence, indent=2) + "\n")
        os.replace(temporary, evidence_path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)
    print(f"{len(programs)} compiled, loaded, round-tripped; {len(smoke)} sym_exec smoke checks; {evidence_path}")


if __name__ == "__main__":
    main()
