#!/usr/bin/env python3
"""Run one profile.toml classifier test and keep stdout, stderr, and the exit code."""

import argparse
import json
import os
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(Path(__file__).resolve().parent))
from doctor import binary  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--program")
    parser.add_argument("--all", action="store_true")
    args = parser.parse_args()
    if args.all == bool(args.program):
        print("pass exactly one of --program NAME or --all", file=sys.stderr)
        sys.exit(2)
    os.chdir(ROOT)
    exe = binary()
    label = "all" if args.all else args.program
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    evidence = ROOT / ".audit" / "verify-classifier" / f"{stamp}-{label}"
    evidence.mkdir(parents=True)
    command = [str(exe), "test"]
    if args.program:
        command.extend(["--program", args.program])
    (evidence / "command.txt").write_text(" ".join(command) + "\n")
    (evidence / "cwd.txt").write_text(str(ROOT) + "\n")
    profile = os.environ.get("CLASSIFIER_PROFILE", str(ROOT / "profile.toml"))
    (evidence / "profile.txt").write_text(profile + "\n")
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
    summary = {"exit": proc.returncode}
    try:
        envelope = json.loads(stdout)
        summary["ok"] = envelope.get("ok")
        summary["payload"] = envelope.get("payload")
        summary["error"] = envelope.get("error")
    except json.JSONDecodeError:
        summary["stdout_json"] = False
    (evidence / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(evidence)
    sys.exit(proc.returncode)


if __name__ == "__main__":
    main()
