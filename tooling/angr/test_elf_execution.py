"""Exercise the formal CLI on ELF64 eBPF relocatable objects."""

import json
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import unittest


CLI = Path(__file__).with_name("analyze.py")


def insn(code, dst=0, src=0, off=0, imm=0):
    return struct.pack("<BBhi", code, dst | src << 4, off, imm)


def xdp_object(code):
    """A real ELF with one global function in an executable XDP section."""
    strings = b"\0xdp\0.strtab\0.symtab\0.shstrtab\0"
    symbols = bytes(24) + struct.pack("<IBBHQQ", 1, 0x12, 0, 1, 0, len(code))
    chunks = (code, b"\0entry\0", symbols, strings)
    image = bytearray(64)
    headers = [bytes(64)]
    for payload, name, kind, flags, link, info, align, entsize in zip(
        chunks, (1, 5, 13, 21), (1, 3, 2, 3), (6, 0, 0, 0),
        (0, 0, 2, 0), (0, 0, 1, 0), (8, 1, 8, 1), (0, 0, 24, 0),
    ):
        image += bytes(-len(image) % align)
        headers.append(struct.pack("<IIQQQQIIQQ", name, kind, flags, 0,
                                   len(image), len(payload), link, info, align, entsize))
        image += payload
    image += bytes(-len(image) % 8)
    shoff = len(image)
    image += b"".join(headers)
    ident = b"\x7fELF\x02\x01\x01" + bytes(9)
    image[:64] = struct.pack("<16sHHIQQQIHHHHHH", ident, 1, 247, 1, 0, 0,
                             shoff, 0, 64, 0, 0, 64, len(headers), 4)
    return image


class ElfExecutionTest(unittest.TestCase):
    def run_elf(self, instructions, case, *options, error=None):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            obj, spec, out = root / "entry.o", root / "spec.json", root / "report"
            obj.write_bytes(xdp_object(b"".join(instructions)))
            spec.write_text(json.dumps({"cases": [{"id": "behavior", **case}]}))
            result = subprocess.run([sys.executable, CLI, "analyze-object", obj,
                                     "--spec", spec, "--out", out, *options],
                                    capture_output=True, text=True, timeout=45)
            if error:
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn(error, result.stderr)
                return None
            self.assertEqual(result.returncode, 0, result.stderr)
            return json.loads((out / "cases/behavior/result.json").read_text())

    def test_valid_mov_and_reserved_fields(self):
        spec = {"input": {"packet_hex": ""}, "expect": [{"action": 1}]}
        report = self.run_elf([insn(0xb7, imm=1), insn(0x95)], spec)
        self.assertEqual(report["verdict"], "holds")
        self.assertEqual(report["exits"][0]["action"], 1)
        self.assertEqual(report["reachable_gaps"]["status"], "unsat")
        self.run_elf([insn(0xb7, off=7, imm=1), insn(0x95)], spec, error="slot 0")

    def test_unsigned_division_and_modulo_with_symbolic_divisor(self):
        read_byte = [insn(0x61, dst=3, src=1), insn(0x71, dst=2, src=3)]
        small = [{"bytes": {"0": value}} for value in (0, 1, 2)]
        other = {"all": [{"not": when} for when in small]}
        for opcode, answers in ((0x3c, (0, 2, 1, 0)), (0x3f, (0, 2, 1, 0)),
                                (0x9c, (2, 0, 0, 2)), (0x9f, (2, 0, 0, 2))):
            with self.subTest(opcode=hex(opcode)):
                case = {"input": {"packet_hex": "00", "symbolic_bytes": [0]},
                        "expect": [{"when": when, "action": action}
                                   for when, action in zip([*small, other], answers)]}
                result = self.run_elf([
                    *read_byte, insn(0xb7, imm=2), insn(opcode, src=2), insn(0x95),
                ], case)
                self.assertEqual(result["verdict"], "holds", result)

        for opcode in (0x37, 0x34, 0x97, 0x94):
            with self.subTest(signed=hex(opcode)):
                self.run_elf([insn(0xb7, imm=2), insn(opcode, off=1, imm=1), insn(0x95)],
                             case, error="invalid or unsupported ALU encoding")

    def test_alu32_zero_extension_and_64_bit_immediate_sign_extension(self):
        case = {"input": {"packet_hex": ""}, "expect": [{"action": 1}]}
        result = self.run_elf([
            insn(0xb7, dst=2, imm=-1),
            insn(0xc5, dst=2, off=1),  # JS64: -1 < 0
            insn(0x05, off=6),
            insn(0x04, dst=2, imm=0),  # r2 = (u32)-1
            insn(0x25, dst=2, off=1, imm=0x7fffffff),
            insn(0x05, off=3),
            insn(0xd5, dst=2, off=2),  # JS64: r2 <= 0 is false
            insn(0xb7, imm=1),
            insn(0x95),
            insn(0xb7, imm=2),
            insn(0x95),
        ], case)
        self.assertEqual(result["verdict"], "holds", result)
        self.run_elf([insn(0xbf, dst=0, src=1, off=8), insn(0x95)], case,
                     error="invalid or unsupported ALU encoding")

    def test_endian_widths(self):
        for opcode, width, expected in ((0xd4, 16, 0x2211), (0xdc, 16, 0x1122),
                                        (0xd4, 32, 0x44332211), (0xdc, 32, 0x11223344),
                                        (0xd4, 64, 0x44332211), (0xdc, 64, 0x55667788)):
            with self.subTest(opcode=hex(opcode), width=width):
                result = self.run_elf([
                    insn(0x18, imm=0x44332211), insn(0, imm=-0x778899ab),
                    insn(opcode, imm=width), insn(0x95),
                ], {"input": {"packet_hex": ""}, "expect": [{"action": expected}]})
                self.assertEqual(result["verdict"], "holds", result)

    def test_finite_symbolic_loop_and_uncovered_back_edge(self):
        loop = [insn(0x61, dst=3, src=1), insn(0x71, dst=2, src=3),
                insn(0x54, dst=2, imm=3), insn(0xb7, imm=1),
                insn(0x15, dst=2, off=2), insn(0x14, dst=2, imm=1),
                insn(0x05, off=-3), insn(0x95)]
        case = {"input": {"packet_hex": "00", "symbolic_bytes": [0]}, "expect": [{"action": 1}]}
        result = self.run_elf(loop, case)
        self.assertEqual(result["verdict"], "holds", result)
        self.assertEqual(len(result["exits"]), 4)
        self.assertEqual(result["overlap"]["status"], "unsat")
        gap = self.run_elf(loop, case, "--max-back-edges", "0")
        self.assertEqual(gap["verdict"], "undetermined")
        self.assertEqual(gap["reachable_gaps"]["status"], "sat")
        self.assertEqual([g["kind"] for g in gap["unresolved"]], ["loop_budget"])
        self.assertNotEqual(int(gap["uncovered_input"]["packet_hex"], 16) & 3, 0)

    def test_gaps_and_missing_spec_paths(self):
        case = {"input": {"packet_hex": "00", "symbolic_bytes": [0]}, "expect": [{"action": 1}]}
        mov, exit_ = insn(0xb7, imm=1), insn(0x95)
        faults = [
            ([insn(0x85, imm=666)], "unknown_helper"),
            ([insn(0x30)], "unsupported_instruction"),
            ([insn(0x61, dst=2, src=10, off=-4)], "exception"),
            ([insn(0xbf, dst=2, src=9)], "exception"),
            ([insn(0x61, dst=3, src=1), insn(0x71, dst=2, src=3),
              insn(0x0f, dst=3, src=2), insn(0x71, dst=2, src=3)], "symbolic_address"),
            ([insn(0x62, dst=1, off=4)], "exception"),  # invalid final data_end
        ]
        for bad, kind in faults:
            with self.subTest(kind=kind, opcode=bad[0].hex()):
                result = self.run_elf([*bad, mov, exit_], case)
                self.assertEqual(result["verdict"], "undetermined", result)
                self.assertEqual(result["reachable_gaps"]["status"], "sat")
                self.assertEqual([g["kind"] for g in result["unresolved"]], [kind])
        result = self.run_elf([mov, exit_], {**case, "expect": [
            {"when": {"bytes": {"0": 0}}, "action": 1},
        ]})
        self.assertEqual(result["verdict"], "undetermined")
        self.assertEqual(result["coverage"]["status"], "unsat")
        self.assertEqual(result["spec_coverage"]["status"], "sat")

    def test_exit_observes_only_the_valid_packet_range(self):
        result = self.run_elf([
            insn(0x61, dst=2, src=1),
            insn(0x72, dst=2, imm=0xaa),
            insn(0x62, dst=1, off=4, imm=0x10001),
            insn(0xb7, imm=1), insn(0x95),
        ], {"input": {"packet_hex": "0000"}, "expect": [
            {"action": 1, "bytes": {"0": 0xaa}, "context": {"4": 1}},
        ]})
        self.assertEqual(result["verdict"], "holds", result)
        exit_, = result["exits"]
        self.assertEqual(exit_["packet_range"], {"start": 0, "end": 1})
        self.assertEqual(exit_["packet"], {"origin": 0, "hex": "aa"})
        self.assertEqual(exit_["events"], [
            {"kind": "write", "resource": "packet", "pc": 1,
             "offset": 0, "width": 1, "value": 0xaa},
            {"kind": "write", "resource": "context", "pc": 2,
             "offset": 4, "width": 4, "value": 0x10001},
        ])


if __name__ == "__main__":
    unittest.main()
