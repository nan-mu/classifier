#!/usr/bin/env python3
"""Stop a drive this skill started. Leaves the evidence directory in place."""

import os
import signal
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]


def main() -> None:
    if len(sys.argv) != 2:
        print("usage: cleanup.py EVIDENCE_DIR", file=sys.stderr)
        sys.exit(2)
    evidence = Path(sys.argv[1]).resolve()
    root = (ROOT / ".audit" / "verify-classifier").resolve()
    if root not in evidence.parents:
        print(f"{evidence} is outside {root}", file=sys.stderr)
        sys.exit(2)
    pid_path = evidence / "pid"
    if not pid_path.is_file():
        print(f"no pid in {evidence}")
        return
    pid = int(pid_path.read_text().strip())
    try:
        os.kill(pid, 0)
    except OSError:
        print(f"pid {pid} is not running")
        return
    os.kill(pid, signal.SIGTERM)
    print(f"sent SIGTERM to {pid}")


if __name__ == "__main__":
    main()
