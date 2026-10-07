#!/usr/bin/env python3
"""Decode esp32c3.bin with Sail-named encdec_* and check the stream."""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))

from decode_imc import decode_image  # noqa: E402

BIN = ROOT / "esp32c3.bin"

# Expected (offset, size, ctor) for the fixture. Lengths match classifier
# InstructionTable / riscv_isa partitioning; ctors are Sail instruction names.
EXPECTED = [
    (0x00, 2, "C_LW"),
    (0x02, 2, "C_LW"),
    (0x04, 4, "ITYPE"),
    (0x08, 2, "C_LI"),
    (0x0A, 4, "BTYPE"),
    (0x0E, 2, "C_ADDI"),
    (0x10, 2, "C_SWSP"),
    (0x12, 2, "C_SWSP"),
    (0x14, 2, "C_ADDI4SPN"),
    (0x16, 4, "LOAD"),
    (0x1A, 2, "C_ADDI"),
    (0x1C, 4, "ITYPE"),
    (0x20, 4, "RTYPE"),
    (0x24, 4, "RTYPE"),
    (0x28, 2, "C_OR"),
    (0x2A, 2, "C_BNEZ"),
    (0x2C, 4, "LOAD"),
    (0x30, 2, "C_LI"),
    (0x32, 4, "BTYPE"),
    (0x36, 4, "LOAD"),
    (0x3A, 2, "C_SLLI"),
    (0x3C, 2, "C_SRLI"),
    (0x3E, 2, "C_ADD"),
    (0x40, 4, "ITYPE"),
    (0x44, 4, "BTYPE"),
    (0x48, 4, "LOAD"),
    (0x4C, 2, "C_LUI"),
    (0x4E, 4, "ITYPE"),
    (0x52, 4, "BTYPE"),
    (0x56, 2, "C_ADDI"),
    (0x58, 4, "UTYPE"),
    (0x5C, 4, "ITYPE"),
    (0x60, 2, "C_LI"),
    (0x62, 2, "C_LI"),
    (0x64, 2, "C_LI"),
    (0x66, 2, "C_LI"),
    (0x68, 2, "C_JAL"),
    (0x6A, 2, "C_MV"),
    (0x6C, 2, "C_LI"),
    (0x6E, 2, "C_BEQZ"),
    (0x70, 2, "C_LW"),
    (0x72, 2, "C_ADDI"),
    (0x74, 2, "C_SW"),
    (0x76, 2, "C_LI"),
    (0x78, 2, "C_LWSP"),
    (0x7A, 2, "C_LWSP"),
    (0x7C, 2, "C_ADDI"),
    (0x7E, 2, "C_JR"),
]


def main() -> int:
    data = BIN.read_bytes()
    got = decode_image(data)

    if len(got) != len(EXPECTED):
        print(f"FAIL count: got {len(got)} want {len(EXPECTED)}", file=sys.stderr)
        for d in got:
            print(f"  {d.offset:04x} len={d.size} {d.ctor} {d.detail}", file=sys.stderr)
        return 1

    bad = False
    for d, (off, size, ctor) in zip(got, EXPECTED):
        if d.offset != off or d.size != size or d.ctor != ctor:
            print(
                f"FAIL @{off:#04x}: got ({d.offset:#04x},{d.size},{d.ctor}) "
                f"want ({off:#04x},{size},{ctor}) detail={d.detail}",
                file=sys.stderr,
            )
            bad = True
        if d.ctor in ("ILLEGAL", "C_ILLEGAL"):
            print(f"FAIL illegal at {d.offset:#04x}: {d.detail}", file=sys.stderr)
            bad = True

    if bad:
        return 1

    print(f"ok: {BIN.name} → {len(got)} insns via encdec_*/encdec_compressed_*")
    for d in got[:5]:
        print(f"  {d.offset:04x} {d.ctor} {d.detail}")
    print("  …")
    print(f"  {got[-1].offset:04x} {got[-1].ctor} {got[-1].detail}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
