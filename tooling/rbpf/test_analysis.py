"""Regressions for coverage, ordered helpers, and output range in the rBPF model."""

import struct
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from analysis import Limits, run_case
from analyze import Program
from machine import Map, PACKET, decode


def instruction(code, dst=0, src=0, offset=0, imm=0):
    return struct.pack("<BBhi", code, dst | src << 4, offset, imm)


def run(instructions, domain, expect, maps=(), back_edges=16):
    program = Program("test", "", "", maps, decode(b"".join(instructions), len(maps)))
    spec = {"id": "test", "input": domain, "expect": expect}
    with TemporaryDirectory() as temp:
        return run_case(program, spec, Path(temp) / "case", Limits(256, back_edges, 32, 2000))


class AnalysisTest(unittest.TestCase):
    def test_partial_expectation_has_a_spec_gap(self):
        report = run([instruction(0xb4, imm=1), instruction(0x95)],
                     {"packet_hex": "ff", "lengths": [0, 1]},
                     [{"when": {"length": 1}, "action": 1}])
        self.assertEqual(report["verdict"], "undetermined")
        self.assertEqual(report["coverage"]["status"], "unsat")
        self.assertEqual(report["spec_coverage"]["status"], "sat")
        self.assertEqual(report["comparison"]["status"], "unsat")
        self.assertEqual(report["unspecified_input"]["lengths"], [0])

    def test_empty_domain_stops_before_coverage(self):
        report = run([instruction(0xb4, imm=1), instruction(0x95)],
                     {"packet_hex": "", "lengths": []}, [{"action": 1}])
        self.assertEqual(report["verdict"], "empty_domain")
        self.assertNotIn("coverage", report)

    def test_gaps_preserve_uncovered_inputs(self):
        cases = {
            "unknown_helper": [instruction(0x85, imm=99)],
            "loop_budget": [instruction(0x05, offset=-1)],
            "exception": [instruction(0x71, src=10, offset=-1), instruction(0x95)],
            "symbolic_address": [
                instruction(0x61, dst=2, src=1), instruction(0x71, dst=3, src=2),
                instruction(0x0f, dst=2, src=3), instruction(0x71, src=2), instruction(0x95),
            ],
        }
        for kind, instructions in cases.items():
            with self.subTest(kind=kind):
                report = run(instructions, {"packet_hex": "0001", "symbolic_bytes": [0]},
                             [{"action": 1}], back_edges=0)
                self.assertEqual(report["verdict"], "undetermined")
                self.assertEqual(report["coverage"]["status"], "sat")
                self.assertEqual([gap["kind"] for gap in report["unresolved"]], [kind])
                self.assertEqual(report["uncovered_input"]["lengths"], [2])

    def test_lookup_captures_each_key_before_packet_mutation(self):
        call = [instruction(0x18, dst=1, src=1), instruction(0),
                instruction(0xbf, dst=2, src=7), instruction(0x85, imm=1)]
        instructions = [
            instruction(0x61, dst=7, src=1), *call,
            instruction(0x72, imm=0x22),  # store through the first lookup pointer
            instruction(0x72, dst=7, imm=0x02), *call,
            instruction(0xb4, imm=2), instruction(0x95),
        ]
        maps = (Map("table", 1, 4, 0x300, 1, 1),)
        key = {"map": "table", "key": "01"}
        domain = {"packet_hex": "01", "map": [{**key, "present": True, "value": 16}]}
        expected = [{"action": 2, "bytes": {"0": 2}, "map": [{**key, "value": 0x22}],
                     "helpers": [{"helper": 1, **key, "present": True},
                                 {"helper": 1, "map": "table", "key": "02", "present": False}]}]
        report = run(instructions, domain, expected, maps)
        self.assertEqual(report["verdict"], "holds")
        events = report["exits"][0]["events"]
        self.assertEqual([event["pc"] for event in events], [4, 5, 6, 10])
        self.assertEqual([event.get("key") for event in events], ["01", "01", None, "02"])
        self.assertEqual(events[1]["width"], 1)
        self.assertEqual(events[1]["value"], 0x22)

    def test_observation_uses_exit_packet_range(self):
        report = run([instruction(0x62, dst=1, imm=PACKET + 1),
                      instruction(0xb7, imm=-1), instruction(0x95)],
                     {"packet_hex": "aabbcc"},
                     [{"context": {"0": 1}, "action": 0xffffffff}])
        self.assertEqual(report["verdict"], "holds")
        path = report["exits"][0]
        self.assertEqual(path["action"], 0xffffffff)
        self.assertEqual(path["packet_range"], {"start": 1, "end": 3})
        self.assertEqual(path["packet"], {"hex": "bbcc", "origin": 1})
        self.assertEqual(path["events"][0]["resource"], "context")


if __name__ == "__main__":
    unittest.main()
