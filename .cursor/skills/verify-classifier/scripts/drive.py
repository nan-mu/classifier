#!/usr/bin/env python3
"""Run one classifier gate and keep stdout, stderr, and the exit code."""

import argparse
import os
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]

GATES = {
    "profile": [
        "cargo",
        "test",
        "--manifest-path",
        "tooling/Cargo.toml",
        "-p",
        "server",
        "--test",
        "profile_expect",
        "--",
        "--nocapture",
    ],
    "formal": ["lake", "build", "Verification"],
    "rust": [
        "cargo",
        "test",
        "--manifest-path",
        "tooling/Cargo.toml",
        "--workspace",
        "--lib",
        "--bins",
        "--tests",
        "--",
        "--skip",
        "profile_programs_match_expect",
    ],
}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--gate", choices=sorted(GATES), required=True)
    args = parser.parse_args()
    os.chdir(ROOT)
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    evidence = ROOT / ".audit" / "verify-classifier" / f"{stamp}-{args.gate}"
    evidence.mkdir(parents=True)
    command = GATES[args.gate]
    (evidence / "command.txt").write_text(" ".join(command) + "\n")
    (evidence / "cwd.txt").write_text(str(ROOT) + "\n")
    proc = subprocess.Popen(
        command,
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    (evidence / "pid").write_text(str(proc.pid) + "\n")
    stdout, stderr = proc.communicate()
    (evidence / "stdout.txt").write_text(stdout)
    (evidence / "stderr.txt").write_text(stderr)
    (evidence / "exit_code.txt").write_text(str(proc.returncode) + "\n")
    print(evidence)
    sys.exit(proc.returncode)


if __name__ == "__main__":
    main()
