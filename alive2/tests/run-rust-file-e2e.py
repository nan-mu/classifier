#!/usr/bin/env python3
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tomllib


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(args):
    result = subprocess.run([str(arg) for arg in args], capture_output=True, text=True, timeout=30)
    if result.returncode:
        raise RuntimeError(f"{args}: exit {result.returncode}: {result.stderr}")
    return result.stdout


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--compiler", type=Path, required=True)
    parser.add_argument("--loader", type=Path, required=True)
    parser.add_argument("--index", type=Path, required=True)
    parser.add_argument("--out-dir", type=Path, required=True)
    args = parser.parse_args()
    snapshot = tomllib.loads(args.index.read_text())
    run([args.compiler, "compile-corpus", "--index", args.index, "--out-dir", args.out_dir])
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
        assert report["status"] == "converted"
        assert report["implementation_proof"] == "not_proven"
        assert len(metadata["instructions"]) == report["instructions"]
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
        "programs": programs, "smoke": smoke,
    }
    evidence_path = args.out_dir / "verification.json"
    evidence_path.write_text(json.dumps(evidence, indent=2) + "\n")
    print(f"{len(programs)} compiled, loaded, round-tripped; {len(smoke)} sym_exec smoke checks; {evidence_path}")


if __name__ == "__main__":
    main()
