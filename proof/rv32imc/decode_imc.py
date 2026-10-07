#!/usr/bin/env python3
"""RV32IMC decode mirroring Sail encdec_backwards / encdec_compressed_backwards.

Returns Sail-style constructor names used in LeanRV32IMC.Instruction.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterator


@dataclass(frozen=True)
class Decoded:
    offset: int
    size: int
    word: int
    ctor: str
    detail: str


def _bits(x: int, hi: int, lo: int) -> int:
    return (x >> lo) & ((1 << (hi - lo + 1)) - 1)


def _sign(v: int, width: int) -> int:
    sign = 1 << (width - 1)
    return (v & (sign - 1)) - (v & sign)


def _reg(x: int) -> int:
    return x & 0x1F


def _creg(x: int) -> int:
    return 8 + (x & 0x7)


def encdec_compressed_backwards(h: int) -> tuple[str, str]:
    """Sail: encdec_compressed_backwards (BitVec 16 → instruction)."""
    h &= 0xFFFF
    op = h & 0x3
    funct3 = _bits(h, 15, 13)

    if op == 0b00:
        if funct3 == 0b000:
            nzuimm = (
                (_bits(h, 10, 7) << 6)
                | (_bits(h, 12, 11) << 4)
                | (_bits(h, 5, 5) << 3)
                | (_bits(h, 6, 6) << 2)
            )
            rd = _creg(_bits(h, 4, 2))
            if nzuimm == 0:
                return "C_ILLEGAL", f"half=0x{h:04x}"
            return "C_ADDI4SPN", f"rd=x{rd} nzuimm={nzuimm}"
        if funct3 == 0b010:
            uimm = (_bits(h, 5, 5) << 6) | (_bits(h, 12, 10) << 3) | (_bits(h, 6, 6) << 2)
            rs1 = _creg(_bits(h, 9, 7))
            rd = _creg(_bits(h, 4, 2))
            return "C_LW", f"rd=x{rd} rs1=x{rs1} uimm={uimm}"
        if funct3 == 0b110:
            uimm = (_bits(h, 5, 5) << 6) | (_bits(h, 12, 10) << 3) | (_bits(h, 6, 6) << 2)
            rs1 = _creg(_bits(h, 9, 7))
            rs2 = _creg(_bits(h, 4, 2))
            return "C_SW", f"rs1=x{rs1} rs2=x{rs2} uimm={uimm}"
        return "C_ILLEGAL", f"half=0x{h:04x}"

    if op == 0b01:
        if funct3 == 0b000:
            rd = _reg(_bits(h, 11, 7))
            imm = _sign((_bits(h, 12, 12) << 5) | _bits(h, 6, 2), 6)
            if rd == 0 and imm == 0:
                return "C_NOP", "imm=0"
            if rd == 0:
                return "C_ADDI", f"rd=x0 imm={imm}"  # HINT in some docs; Sail keeps C_ADDI
            return "C_ADDI", f"rd=x{rd} imm={imm}"
        if funct3 == 0b001:
            imm = _sign(
                (_bits(h, 12, 12) << 10)
                | (_bits(h, 8, 8) << 9)
                | (_bits(h, 10, 9) << 7)
                | (_bits(h, 6, 6) << 6)
                | (_bits(h, 7, 7) << 5)
                | (_bits(h, 2, 2) << 4)
                | (_bits(h, 11, 11) << 3)
                | (_bits(h, 5, 3) << 1),
                11,
            )
            return "C_JAL", f"imm={imm}"
        if funct3 == 0b010:
            rd = _reg(_bits(h, 11, 7))
            imm = _sign((_bits(h, 12, 12) << 5) | _bits(h, 6, 2), 6)
            return "C_LI", f"rd=x{rd} imm={imm}"
        if funct3 == 0b011:
            rd = _reg(_bits(h, 11, 7))
            if rd == 2:
                imm = _sign(
                    (_bits(h, 12, 12) << 9)
                    | (_bits(h, 4, 3) << 7)
                    | (_bits(h, 5, 5) << 6)
                    | (_bits(h, 2, 2) << 5)
                    | (_bits(h, 6, 6) << 4),
                    10,
                )
                return "C_ADDI16SP", f"imm={imm}"
            imm = _sign((_bits(h, 12, 12) << 5) | _bits(h, 6, 2), 6)
            return "C_LUI", f"rd=x{rd} imm={imm}"
        if funct3 == 0b100:
            funct2 = _bits(h, 11, 10)
            rd = _creg(_bits(h, 9, 7))
            if funct2 == 0b00:
                shamt = (_bits(h, 12, 12) << 5) | _bits(h, 6, 2)
                return "C_SRLI", f"rd=x{rd} shamt={shamt}"
            if funct2 == 0b01:
                shamt = (_bits(h, 12, 12) << 5) | _bits(h, 6, 2)
                return "C_SRAI", f"rd=x{rd} shamt={shamt}"
            if funct2 == 0b10:
                imm = _sign((_bits(h, 12, 12) << 5) | _bits(h, 6, 2), 6)
                return "C_ANDI", f"rd=x{rd} imm={imm}"
            # funct2 == 0b11
            if _bits(h, 12, 12) == 0:
                rs2 = _creg(_bits(h, 4, 2))
                sel = _bits(h, 6, 5)
                name = {0b00: "C_SUB", 0b01: "C_XOR", 0b10: "C_OR", 0b11: "C_AND"}[sel]
                return name, f"rd=x{rd} rs2=x{rs2}"
            return "C_ILLEGAL", f"half=0x{h:04x}"
        if funct3 == 0b101:
            imm = _sign(
                (_bits(h, 12, 12) << 10)
                | (_bits(h, 8, 8) << 9)
                | (_bits(h, 10, 9) << 7)
                | (_bits(h, 6, 6) << 6)
                | (_bits(h, 7, 7) << 5)
                | (_bits(h, 2, 2) << 4)
                | (_bits(h, 11, 11) << 3)
                | (_bits(h, 5, 3) << 1),
                11,
            )
            return "C_J", f"imm={imm}"
        if funct3 == 0b110:
            imm = _sign(
                (_bits(h, 12, 12) << 8)
                | (_bits(h, 6, 5) << 6)
                | (_bits(h, 2, 2) << 5)
                | (_bits(h, 11, 10) << 3)
                | (_bits(h, 4, 3) << 1),
                9,
            )
            rs1 = _creg(_bits(h, 9, 7))
            return "C_BEQZ", f"rs1=x{rs1} imm={imm}"
        if funct3 == 0b111:
            imm = _sign(
                (_bits(h, 12, 12) << 8)
                | (_bits(h, 6, 5) << 6)
                | (_bits(h, 2, 2) << 5)
                | (_bits(h, 11, 10) << 3)
                | (_bits(h, 4, 3) << 1),
                9,
            )
            rs1 = _creg(_bits(h, 9, 7))
            return "C_BNEZ", f"rs1=x{rs1} imm={imm}"
        return "C_ILLEGAL", f"half=0x{h:04x}"

    # op == 0b10
    if funct3 == 0b000:
        rd = _reg(_bits(h, 11, 7))
        shamt = (_bits(h, 12, 12) << 5) | _bits(h, 6, 2)
        return "C_SLLI", f"rd=x{rd} shamt={shamt}"
    if funct3 == 0b010:
        rd = _reg(_bits(h, 11, 7))
        uimm = (_bits(h, 3, 2) << 6) | (_bits(h, 12, 12) << 5) | (_bits(h, 6, 4) << 2)
        return "C_LWSP", f"rd=x{rd} uimm={uimm}"
    if funct3 == 0b100:
        rd = _reg(_bits(h, 11, 7))
        rs2 = _reg(_bits(h, 6, 2))
        bit12 = _bits(h, 12, 12)
        if bit12 == 0:
            if rs2 == 0:
                return "C_JR", f"rs1=x{rd}"
            return "C_MV", f"rd=x{rd} rs2=x{rs2}"
        if rd == 0 and rs2 == 0:
            return "C_EBREAK", ""
        if rs2 == 0:
            return "C_JALR", f"rs1=x{rd}"
        return "C_ADD", f"rd=x{rd} rs2=x{rs2}"
    if funct3 == 0b110:
        uimm = (_bits(h, 8, 7) << 6) | (_bits(h, 12, 9) << 2)
        rs2 = _reg(_bits(h, 6, 2))
        return "C_SWSP", f"rs2=x{rs2} uimm={uimm}"
    return "C_ILLEGAL", f"half=0x{h:04x}"


_IOP = {0b000: "ADDI", 0b010: "SLTI", 0b011: "SLTIU", 0b100: "XORI", 0b110: "ORI", 0b111: "ANDI"}
_BOP = {0b000: "BEQ", 0b001: "BNE", 0b100: "BLT", 0b101: "BGE", 0b110: "BLTU", 0b111: "BGEU"}
_ROP = {
    (0b0000000, 0b000): "ADD",
    (0b0100000, 0b000): "SUB",
    (0b0000000, 0b001): "SLL",
    (0b0000000, 0b010): "SLT",
    (0b0000000, 0b011): "SLTU",
    (0b0000000, 0b100): "XOR",
    (0b0000000, 0b101): "SRL",
    (0b0100000, 0b101): "SRA",
    (0b0000000, 0b110): "OR",
    (0b0000000, 0b111): "AND",
}
_LOAD_W = {0b000: (1, True), 0b001: (2, True), 0b010: (4, True), 0b100: (1, False), 0b101: (2, False)}
_STORE_W = {0b000: 1, 0b001: 2, 0b010: 4}


def encdec_backwards(w: int) -> tuple[str, str]:
    """Sail: encdec_backwards (BitVec 32 → instruction). RV32IMC subset."""
    w &= 0xFFFFFFFF
    opcode = w & 0x7F
    rd = _reg(_bits(w, 11, 7))
    funct3 = _bits(w, 14, 12)
    rs1 = _reg(_bits(w, 19, 15))
    rs2 = _reg(_bits(w, 24, 20))
    funct7 = _bits(w, 31, 25)

    if opcode == 0b0110111:
        imm = _bits(w, 31, 12)
        return "UTYPE", f"LUI rd=x{rd} imm=0x{imm:x}"
    if opcode == 0b0010111:
        imm = _bits(w, 31, 12)
        return "UTYPE", f"AUIPC rd=x{rd} imm=0x{imm:x}"
    if opcode == 0b1101111:
        imm = (
            (_bits(w, 31, 31) << 20)
            | (_bits(w, 19, 12) << 12)
            | (_bits(w, 20, 20) << 11)
            | (_bits(w, 30, 21) << 1)
        )
        return "JAL", f"rd=x{rd} imm={_sign(imm, 21)}"
    if opcode == 0b1100111 and funct3 == 0b000:
        imm = _sign(_bits(w, 31, 20), 12)
        return "JALR", f"rd=x{rd} rs1=x{rs1} imm={imm}"
    if opcode == 0b1100011 and funct3 in _BOP:
        imm = (
            (_bits(w, 31, 31) << 12)
            | (_bits(w, 7, 7) << 11)
            | (_bits(w, 30, 25) << 5)
            | (_bits(w, 11, 8) << 1)
        )
        return "BTYPE", f"{_BOP[funct3]} rs1=x{rs1} rs2=x{rs2} imm={_sign(imm, 13)}"
    if opcode == 0b0010011:
        if funct3 in _IOP:
            imm = _sign(_bits(w, 31, 20), 12)
            return "ITYPE", f"{_IOP[funct3]} rd=x{rd} rs1=x{rs1} imm={imm}"
        if funct3 == 0b001 and funct7 == 0b0000000:
            shamt = _bits(w, 24, 20)
            return "SHIFTIOP", f"SLLI rd=x{rd} rs1=x{rs1} shamt={shamt}"
        if funct3 == 0b101 and funct7 == 0b0000000:
            shamt = _bits(w, 24, 20)
            return "SHIFTIOP", f"SRLI rd=x{rd} rs1=x{rs1} shamt={shamt}"
        if funct3 == 0b101 and funct7 == 0b0100000:
            shamt = _bits(w, 24, 20)
            return "SHIFTIOP", f"SRAI rd=x{rd} rs1=x{rs1} shamt={shamt}"
    if opcode == 0b0110011:
        if (funct7, funct3) in _ROP:
            return "RTYPE", f"{_ROP[(funct7, funct3)]} rd=x{rd} rs1=x{rs1} rs2=x{rs2}"
        if funct7 == 0b0000001:
            if funct3 == 0b000:
                return "MUL", f"rd=x{rd} rs1=x{rs1} rs2=x{rs2}"
            if funct3 == 0b100:
                return "DIV", f"rd=x{rd} rs1=x{rs1} rs2=x{rs2} signed"
            if funct3 == 0b101:
                return "DIV", f"rd=x{rd} rs1=x{rs1} rs2=x{rs2} unsigned"
            if funct3 == 0b110:
                return "REM", f"rd=x{rd} rs1=x{rs1} rs2=x{rs2} signed"
            if funct3 == 0b111:
                return "REM", f"rd=x{rd} rs1=x{rs1} rs2=x{rs2} unsigned"
            # MULH / MULHSU / MULHU still MUL-family in Sail as mul_op variants
            if funct3 in (0b001, 0b010, 0b011):
                return "MUL", f"rd=x{rd} rs1=x{rs1} rs2=x{rs2} mulh_funct3={funct3}"
    if opcode == 0b0000011 and funct3 in _LOAD_W:
        width, signed = _LOAD_W[funct3]
        imm = _sign(_bits(w, 31, 20), 12)
        return "LOAD", f"rd=x{rd} rs1=x{rs1} imm={imm} width={width} signed={signed}"
    if opcode == 0b0100011 and funct3 in _STORE_W:
        width = _STORE_W[funct3]
        imm = _sign((_bits(w, 31, 25) << 5) | _bits(w, 11, 7), 12)
        return "STORE", f"rs1=x{rs1} rs2=x{rs2} imm={imm} width={width}"
    if opcode == 0b0001111:
        return "FENCE", f"word=0x{w:08x}"
    if opcode == 0b1110011:
        if w == 0x00000073:
            return "ECALL", ""
        if w == 0x00100073:
            return "EBREAK", ""
        if w == 0x30200073:
            return "MRET", ""
        if w == 0x10200073:
            return "SRET", ""
        if w == 0x10500073:
            return "WFI", ""

    return "ILLEGAL", f"word=0x{w:08x}"


def code_end(bin_bytes: bytes) -> int:
    marker = b"GPL\0"
    i = bin_bytes.find(marker)
    return i if i >= 0 else len(bin_bytes)


def decode_image(bin_bytes: bytes) -> list[Decoded]:
    end = code_end(bin_bytes)
    out: list[Decoded] = []
    off = 0
    while off < end:
        if off + 2 > end:
            raise ValueError(f"truncated at {off:#x}")
        h = int.from_bytes(bin_bytes[off : off + 2], "little")
        if (h & 0x3) != 0x3:
            ctor, detail = encdec_compressed_backwards(h)
            out.append(Decoded(off, 2, h, ctor, detail))
            off += 2
            continue
        if off + 4 > end:
            raise ValueError(f"truncated 32-bit at {off:#x}")
        w = int.from_bytes(bin_bytes[off : off + 4], "little")
        ctor, detail = encdec_backwards(w)
        out.append(Decoded(off, 4, w, ctor, detail))
        off += 4
    return out


def iter_lines(bin_bytes: bytes) -> Iterator[str]:
    for d in decode_image(bin_bytes):
        hexv = f"{d.word:0{d.size * 2}x}"
        yield f"{d.offset:04x} len={d.size} hex={hexv} {d.ctor} {d.detail}".rstrip()
