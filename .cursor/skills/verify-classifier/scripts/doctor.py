#!/usr/bin/env python3
"""Read-only check that the three classifier gates are worth driving."""

import os
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
DYLIBS = (
    "libclassifier_Core.dylib",
    "libclassifier_Node.dylib",
    "libclassifier_RV32.dylib",
    "libclassifier_EBPF.dylib",
)


def fail(message: str) -> None:
    print(message, file=sys.stderr)
    sys.exit(1)


def profile_path() -> Path:
    explicit = os.environ.get("CLASSIFIER_PROFILE")
    if explicit:
        path = Path(explicit)
        if not path.is_file():
            fail(f"CLASSIFIER_PROFILE is not a file: {path}")
        return path
    path = ROOT / "profile.toml"
    if not path.is_file():
        fail(f"missing {path}")
    return path


def strip_comment(line: str) -> str:
    in_quote = False
    for index, ch in enumerate(line):
        if ch == '"':
            in_quote = not in_quote
        elif ch == "#" and not in_quote:
            return line[:index]
    return line


def unquote(value: str, line_no: int) -> str:
    if len(value) >= 2 and value[0] == '"' and value[-1] == '"':
        return value[1:-1]
    fail(f"profile line {line_no}: expected a quoted string")
    return ""


def parse_profile(path: Path) -> tuple[Path, list[tuple[str, Path, Path, str]]]:
    build_rel = None
    programs = []
    cur = None
    for line_no, raw in enumerate(path.read_text().splitlines(), 1):
        line = strip_comment(raw).strip()
        if not line:
            continue
        if line == "[[program]]":
            if cur is not None:
                programs.append(cur)
            cur = {}
            continue
        if "=" not in line:
            fail(f"profile line {line_no}: expected key = value")
        key, value = (part.strip() for part in line.split("=", 1))
        if key == "build":
            if cur is not None:
                fail(f"profile line {line_no}: build belongs at the top")
            build_rel = unquote(value, line_no)
            continue
        if key not in {"name", "elf", "bpf", "expect"}:
            fail(f"profile line {line_no}: unknown key {key}")
        if cur is None:
            fail(f"profile line {line_no}: {key} is outside [[program]]")
        cur[key] = unquote(value, line_no)
    if cur is not None:
        programs.append(cur)
    if not build_rel:
        fail("profile.toml needs build")
    if not programs:
        fail("profile.toml has no [[program]]")
    build = (path.parent / build_rel).resolve()
    rows = []
    for slot in programs:
        if not all(slot.get(k) for k in ("name", "elf", "bpf", "expect")):
            fail("[[program]] needs name, elf, bpf, and expect")
        if slot["expect"] not in {"strict", "weak", "fail"}:
            fail(f"{slot['name']}: expect must be strict, weak, or fail")
        rows.append(
            (
                slot["name"],
                build / slot["elf"],
                build / slot["bpf"],
                slot["expect"],
            )
        )
    return build, rows


def main() -> None:
    os.chdir(ROOT)
    if shutil.which("cargo") is None or shutil.which("lake") is None:
        fail("cargo and lake must be on PATH")
    lakefile = (ROOT / "lakefile.lean").read_text()
    if "lean_lib Verification" not in lakefile:
        fail("lakefile.lean does not declare lean_lib Verification")
    path = profile_path()
    build, rows = parse_profile(path)
    lake_lib = ROOT / ".lake" / "build" / "lib"
    for name in DYLIBS:
        lib = lake_lib / name
        if not lib.is_file():
            fail(f"missing {lib}; run Launch first")
    missing = [str(item) for _, elf, bpf, _ in rows for item in (elf, bpf) if not item.is_file()]
    if missing:
        fail("missing images:\n" + "\n".join(missing))
    print(f"profile {path}")
    print(f"build {build}")
    for name, elf, bpf, expect in rows:
        print(f"program {name} expect {expect}")
        print(f"  elf {elf}")
        print(f"  bpf {bpf}")
    print("doctor ok")


if __name__ == "__main__":
    main()
