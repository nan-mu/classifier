"""Behavior checks for the reconstructed state-graph contract.

These tests observe the validator's accept and reject results. They do not
copy its helper structure.
"""

from __future__ import annotations

import copy
import json
import unittest
from pathlib import Path

from validate_state_graph import ROOT_REQUIRED, validate

ROOT = Path(__file__).resolve().parents[1]
EXAMPLE = ROOT / "examples" / "state-graph.example.json"
SCHEMA = ROOT / "contracts" / "alive2-state-graph.schema.json"


def load_example() -> dict:
    with EXAMPLE.open(encoding="utf-8") as handle:
        return json.load(handle)


def codes(doc: dict) -> set[str]:
    return {err.split(":", 1)[0] for err in validate(doc)}


class ContractTest(unittest.TestCase):
    def test_design_fixture_is_labeled_and_accepted(self) -> None:
        doc = load_example()
        self.assertTrue(doc["fixture"])
        self.assertIn("设计夹具", doc["fixture_banner"])
        self.assertEqual(validate(doc), [])

    def test_schema_keeps_the_named_root_fields(self) -> None:
        schema = json.loads(SCHEMA.read_text(encoding="utf-8"))
        self.assertEqual(list(schema["required"]), list(ROOT_REQUIRED))
        self.assertEqual(schema["properties"]["schema_version"]["enum"], [1, 2])

    def test_duplicate_id_is_rejected(self) -> None:
        doc = load_example()
        doc["nodes"].append(copy.deepcopy(doc["nodes"][0]))
        self.assertIn("duplicate_id", codes(doc))

    def test_missing_edge_endpoint_is_rejected(self) -> None:
        doc = load_example()
        doc["edges"][0]["to"] = "missing"
        self.assertIn("missing_ref", codes(doc))

    def test_term_cycle_is_rejected(self) -> None:
        doc = load_example()
        doc["terms"] = [
            {"id": "a", "op": "id", "sort": {"kind": "bool"}, "args": ["b"]},
            {"id": "b", "op": "id", "sort": {"kind": "bool"}, "args": ["a"]},
        ]
        doc["nodes"][0]["path_condition"] = "a"
        doc["edges"][0]["guard"] = "a"
        self.assertIn("cyclic_term", codes(doc))

    def test_eq_width_mismatch_is_rejected(self) -> None:
        doc = load_example()
        doc["terms"] = [
            {"id": "x", "op": "input", "sort": {"kind": "bv", "width": 64}, "args": []},
            {"id": "y", "op": "input", "sort": {"kind": "bv", "width": 32}, "args": []},
            {"id": "c", "op": "eq", "sort": {"kind": "bool"}, "args": ["x", "y"]},
        ]
        doc["nodes"][0]["path_condition"] = "c"
        doc["edges"][0]["guard"] = "c"
        self.assertIn("width_mismatch", codes(doc))

    def test_unsupported_memory_must_say_so(self) -> None:
        doc = load_example()
        doc["memories"][0]["blocks"] = [{
            "id": "b0",
            "unsupported": "pure ALU fixture has no memory model",
        }]
        doc["nodes"][0]["ir_state"]["memory_status"] = "unsupported"
        self.assertEqual(validate(doc), [])
        del doc["nodes"][0]["ir_state"]["memory_status"]
        self.assertIn("memory_not_recoverable", codes(doc))
        doc = load_example()
        doc["memories"][0]["blocks"] = [{"id": "b0", "summary": "empty", "sha256": "abc"}]
        self.assertIn("memory_not_recoverable", codes(doc))

    def test_guard_must_be_bool(self) -> None:
        doc = load_example()
        doc["terms"].append(
            {"id": "bits", "op": "input", "sort": {"kind": "bv", "width": 1}, "args": []}
        )
        doc["edges"][0]["guard"] = "bits"
        self.assertIn("guard_not_bool", codes(doc))

    def test_origin_hash_must_match(self) -> None:
        doc = load_example()
        doc["program"]["origin"] = {"ir_hash": "ff"}
        self.assertIn("origin_hash_mismatch", codes(doc))

    def test_imported_ebpf_cannot_hide_registers(self) -> None:
        doc = load_example()
        doc["program"]["origin"] = {"ir_hash": doc["program"]["ir_hash"]}
        doc["nodes"][0]["rocq_ebpf"] = {"regset": {"R0": {"kind": "bv", "width": 64, "digits": "0x0"}}, "cstk": []}
        found = codes(doc)
        self.assertIn("ebpf_regs_incomplete", found)
        self.assertIn("missing_field", found)

    def test_no_origin_rejects_a_fake_rocq_view(self) -> None:
        doc = load_example()
        doc["nodes"][0]["rocq_ebpf"] = {"regset": {}}
        self.assertIn("rocq_null_on_origin", codes(doc))

    def test_bound_truncation_needs_a_frontier(self) -> None:
        doc = load_example()
        doc["run"]["truncation"] = {"kind": "bound", "reason": "unroll"}
        self.assertIn("frontier_mismatch", codes(doc))

    def test_frontier_without_a_bound_is_rejected(self) -> None:
        doc = load_example()
        doc["coverage"]["frontier"] = ["n0"]
        self.assertIn("frontier_mismatch", codes(doc))

    def test_collapsed_solver_status_is_rejected(self) -> None:
        doc = load_example()
        doc["nodes"][0]["solver"] = {"status": "unsat_or_unknown"}
        self.assertIn("solver_status_collapsed", codes(doc))

    def test_finished_run_is_not_full_coverage(self) -> None:
        doc = load_example()
        doc["run"]["status"] = "finished"
        doc["coverage"]["all_inputs_covered"] = "established"
        self.assertIn("established_without_evidence", codes(doc))

    def test_wide_integer_must_be_a_string(self) -> None:
        doc = load_example()
        doc["memories"][0]["blocks"][0]["offset"] = 2**64
        self.assertIn("js_number_for_bv", codes(doc))

    def test_empty_environment_is_not_an_unsupported_model(self) -> None:
        doc = load_example()
        doc["environment"]["helpers"] = []
        self.assertIn("environment_disguised_empty", codes(doc))

    def test_callstack_frame_must_be_complete(self) -> None:
        doc = load_example()
        doc["program"]["origin"] = {"ir_hash": doc["program"]["ir_hash"]}
        regs = {key: {"kind": "bv", "width": 64, "digits": "0x0"} for key in (
            "R0", "R1", "R2", "R3", "R4", "R5", "R6", "R7", "R8", "R9", "R10", "RAX", "PC"
        )}
        doc["nodes"][0]["rocq_ebpf"] = {
            "regset": regs,
            "cstk": [{"stk_ra": regs["R0"]}],
            "code_id": "main",
            "tail_call_count": "0",
            "mem": "mem0",
        }
        self.assertIn("ebpf_frame_incomplete", codes(doc))


if __name__ == "__main__":
    unittest.main()
