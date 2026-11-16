"""Check an Alive2 state graph against the constraints named in the task.

The author file contracts/alive2-state-graph.schema.json was not in this
workspace. This module is the reconstructed check, not a copy of that file.
"""

from __future__ import annotations

import json
import sys
from typing import Any

ROOT_REQUIRED = (
    "schema",
    "schema_version",
    "fixture",
    "run",
    "program",
    "environment",
    "terms",
    "memories",
    "nodes",
    "edges",
    "coverage",
    "evidence",
)
REG_KEYS = tuple(f"R{i}" for i in range(11)) + ("RAX", "PC")
FRAME_KEYS = ("stk_ra", "stk_r6", "stk_r7", "stk_r8", "stk_r9", "stk_r10")
EDGE_KINDS = {"step", "taken", "not_taken", "merge", "exit", "boundary"}
NODE_STATES = {"normal", "exit", "bound_truncated", "stuck", "ub", "unsupported"}
RUN_STATES = {"created", "running", "finished", "stopped", "failed"}
COVERED = {"established", "not_established", "not_applicable"}
SOLVER = {"sat", "unsat", "unknown", "not_run", "timeout"}
COLLAPSED = {
    "unsat_or_unknown",
    "unsat/unknown",
    "unknown_or_unsat",
    "mixed",
    "unsat|unknown",
}
EVIDENCE_KINDS = {
    "test",
    "smt",
    "artifact_proof",
    "implementation_proof",
    "model_proof",
    "concrete_correspondence",
    "symbolic_correspondence",
}
TRUNCATION = {"none", "bound", "resource", "unsupported"}
ENV_KEYS = (
    "main_program",
    "code_table",
    "jump_table",
    "addr_map",
    "helpers",
    "input_objects",
    "global_reserved",
)
DIGIT_KEYS = {"digits", "offset", "address", "tail_call_count"}
JS_MAX = 2**53 - 1


def validate(doc: Any) -> list[str]:
    errs: list[str] = []
    if not isinstance(doc, dict):
        return ["missing_field: $: root must be an object"]
    for key in ROOT_REQUIRED:
        if key not in doc:
            errs.append(f"missing_field: $.{key}: required")
    if errs:
        return errs
    if doc["schema"] != "alive2-state-graph":
        errs.append("missing_field: $.schema: must be alive2-state-graph")
    if doc["schema_version"] != 1:
        errs.append("missing_field: $.schema_version: must be 1")
    if not isinstance(doc["fixture"], bool):
        errs.append("missing_field: $.fixture: must be bool")

    terms = _index(doc["terms"], "terms", errs)
    memories = _index(doc["memories"], "memories", errs)
    nodes = _index(doc["nodes"], "nodes", errs)
    edges = _index(doc["edges"], "edges", errs)
    _index(doc["evidence"], "evidence", errs)

    _cycles(terms, errs)
    _terms(terms, errs)
    recoverable, explicit_mem = _memories(memories, errs)
    _walk_numbers(doc, "$", errs)
    _program(doc["program"], errs)
    _run(doc["run"], errs)
    _environment(doc["environment"], errs)
    origin = _has_origin(doc["program"])
    _nodes(doc["nodes"], terms, memories, recoverable, explicit_mem, origin, errs)
    _edges(doc["edges"], nodes, terms, errs)
    _coverage(doc, nodes, errs)
    _evidence_records(doc["evidence"], nodes, edges, errs)
    _solver_fields(doc, "$", errs)
    return errs


def _index(items: Any, label: str, errs: list[str]) -> dict[str, dict[str, Any]]:
    found: dict[str, dict[str, Any]] = {}
    if not isinstance(items, list):
        errs.append(f"missing_field: $.{label}: must be a list")
        return found
    for i, item in enumerate(items):
        if not isinstance(item, dict) or not isinstance(item.get("id"), str):
            errs.append(f"missing_field: $.{label}[{i}].id: required string")
            continue
        ident = item["id"]
        if ident in found:
            errs.append(f"duplicate_id: $.{label}.{ident}: duplicate")
        found[ident] = item
    return found


def _cycles(terms: dict[str, dict[str, Any]], errs: list[str]) -> None:
    color: dict[str, int] = {}

    def walk(ident: str) -> None:
        color[ident] = 1
        term = terms.get(ident)
        args = term.get("args", []) if term else []
        if isinstance(args, list):
            for arg in args:
                if not isinstance(arg, str) or arg not in terms:
                    continue
                state = color.get(arg, 0)
                if state == 1:
                    errs.append(f"cyclic_term: $.terms.{ident}: cycle through {arg}")
                elif state == 0:
                    walk(arg)
        color[ident] = 2

    for ident in terms:
        if color.get(ident, 0) == 0:
            walk(ident)


def _terms(terms: dict[str, dict[str, Any]], errs: list[str]) -> None:
    for ident, term in terms.items():
        sort = term.get("sort")
        op = term.get("op")
        if not isinstance(op, str) or not isinstance(sort, dict):
            errs.append(f"missing_field: $.terms.{ident}: op and sort required")
            continue
        kind = sort.get("kind")
        if kind not in {"bv", "bool", "pointer", "undef", "poison", "float", "aggregate", "unsupported"}:
            errs.append(f"width_mismatch: $.terms.{ident}: unknown sort {kind}")
        if kind == "bv":
            width = sort.get("width")
            if not isinstance(width, int) or isinstance(width, bool) or width <= 0:
                errs.append(f"width_mismatch: $.terms.{ident}: bv sort needs a positive width")
        args = term.get("args", [])
        if not isinstance(args, list):
            errs.append(f"missing_field: $.terms.{ident}.args: must be a list")
            continue
        for arg in args:
            if not isinstance(arg, str) or arg not in terms:
                errs.append(f"missing_ref: $.terms.{ident}: arg {arg} missing")
                continue
            if op in {"bvadd", "bvsub", "eq"} and kind == "bv":
                aw = terms[arg].get("sort", {}).get("width")
                if aw != sort.get("width"):
                    errs.append(f"width_mismatch: $.terms.{ident}: arg {arg} width {aw}")
        if op == "eq":
            if kind != "bool":
                errs.append(f"width_mismatch: $.terms.{ident}: eq must be bool")
            widths = [
                terms[arg].get("sort", {}).get("width")
                for arg in args
                if isinstance(arg, str) and arg in terms
            ]
            if len(widths) >= 2 and widths[0] != widths[1]:
                errs.append(f"width_mismatch: $.terms.{ident}: eq arg widths differ")


def _memories(memories: dict[str, dict[str, Any]], errs: list[str]) -> tuple[set[str], set[str]]:
    recoverable: set[str] = set()
    explicit: set[str] = set()
    for ident, mem in memories.items():
        blocks = mem.get("blocks")
        if not isinstance(blocks, list) or "next_block" not in mem:
            errs.append(f"memory_not_recoverable: $.memories.{ident}: blocks and next_block required")
            continue
        good = True
        gaps = 0
        payloads = 0
        for i, block in enumerate(blocks):
            if not isinstance(block, dict):
                good = False
                errs.append(f"memory_not_recoverable: $.memories.{ident}.blocks[{i}]: not an object")
                continue
            reason = block.get("unsupported")
            payload = block.get("bytes", block.get("cells"))
            has_payload = isinstance(payload, list) and bool(payload)
            if isinstance(reason, str) and reason:
                if has_payload:
                    good = False
                    errs.append(
                        f"memory_not_recoverable: $.memories.{ident}.blocks[{i}]: unsupported block also has bytes"
                    )
                gaps += 1
                continue
            summary_only = "sha256" in block or "summary" in block
            if not has_payload:
                good = False
                errs.append(
                    f"memory_not_recoverable: $.memories.{ident}.blocks[{i}]: need bytes or cells, not a hash summary"
                    if summary_only
                    else f"memory_not_recoverable: $.memories.{ident}.blocks[{i}]: bytes or cells required"
                )
            else:
                payloads += 1
            for field in ("init", "current_perm", "max_perm", "provenance"):
                if field not in block:
                    good = False
                    errs.append(f"memory_not_recoverable: $.memories.{ident}.blocks[{i}].{field}: required")
        if not good:
            continue
        if gaps and payloads:
            errs.append(f"memory_not_recoverable: $.memories.{ident}: mixed recoverable and unsupported blocks")
        elif gaps:
            explicit.add(ident)
        else:
            recoverable.add(ident)
    return recoverable, explicit


def _walk_numbers(value: Any, path: str, errs: list[str]) -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            child_path = f"{path}.{key}"
            if key in DIGIT_KEYS and isinstance(child, (int, float)) and not isinstance(child, bool):
                errs.append(f"js_number_for_bv: {child_path}: wide value must be a string")
            elif isinstance(child, int) and not isinstance(child, bool) and abs(child) > JS_MAX:
                errs.append(f"js_number_for_bv: {child_path}: exceeds the JS safe integer range")
            else:
                _walk_numbers(child, child_path, errs)
    elif isinstance(value, list):
        for i, child in enumerate(value):
            _walk_numbers(child, f"{path}[{i}]", errs)


def _program(program: Any, errs: list[str]) -> None:
    if not isinstance(program, dict):
        errs.append("missing_field: $.program: must be an object")
        return
    for key in ("ir_hash", "functions", "instructions"):
        if key not in program:
            errs.append(f"missing_field: $.program.{key}: required")
    origin = program.get("origin")
    if isinstance(origin, dict) and "ir_hash" in origin and origin["ir_hash"] != program.get("ir_hash"):
        errs.append("origin_hash_mismatch: $.program.origin.ir_hash: differs from program.ir_hash")


def _has_origin(program: Any) -> bool:
    if not isinstance(program, dict):
        return False
    origin = program.get("origin")
    return origin not in (None, {})


def _run(run: Any, errs: list[str]) -> None:
    if not isinstance(run, dict):
        errs.append("missing_field: $.run: must be an object")
        return
    for key in ("id", "status", "initial_id", "engine_pin", "unroll_bound", "budgets", "truncation"):
        if key not in run:
            errs.append(f"missing_field: $.run.{key}: required")
    if run.get("status") not in RUN_STATES:
        errs.append(f"missing_field: $.run.status: unknown {run.get('status')}")
    truncation = run.get("truncation")
    if isinstance(truncation, dict) and truncation.get("kind") not in TRUNCATION:
        errs.append(f"frontier_mismatch: $.run.truncation.kind: unknown {truncation.get('kind')}")


def _environment(env: Any, errs: list[str]) -> None:
    if not isinstance(env, dict):
        errs.append("missing_field: $.environment: must be an object")
        return
    for key in ENV_KEYS:
        if key not in env:
            errs.append(f"missing_field: $.environment.{key}: required")
            continue
        value = env[key]
        if key == "global_reserved":
            _global(value, errs)
            continue
        if value in (None, [], {}):
            errs.append(f"environment_disguised_empty: $.environment.{key}: null or empty is not an unsupported model")
        elif isinstance(value, dict) and "unsupported" not in value and "version" not in value and "entries" not in value:
            errs.append(f"missing_field: $.environment.{key}: versioned table, entries, or unsupported")


def _global(value: Any, errs: list[str]) -> None:
    if not isinstance(value, dict):
        errs.append("missing_field: $.environment.global_reserved: must be an object")
        return
    if value.get("threading") != "single":
        errs.append("missing_field: $.environment.global_reserved.threading: this round is single")
    for key in ("thread_pool", "env", "gm", "atom_bit"):
        slot = value.get(key)
        if not isinstance(slot, dict) or slot.get("status") != "unsupported":
            errs.append(f"missing_field: $.environment.global_reserved.{key}: reserved unsupported, not verified")


def _nodes(
    items: Any,
    terms: dict[str, dict[str, Any]],
    memories: dict[str, dict[str, Any]],
    recoverable: set[str],
    explicit_mem: set[str],
    origin: bool,
    errs: list[str],
) -> None:
    if not isinstance(items, list):
        return
    for node in items:
        if not isinstance(node, dict) or not isinstance(node.get("id"), str):
            continue
        ident = node["id"]
        for key in ("location", "unroll", "state", "path_condition", "ir_state", "rocq_ebpf", "evidence_ids"):
            if key not in node:
                errs.append(f"missing_field: $.nodes.{ident}.{key}: required")
        if node.get("state") not in NODE_STATES:
            errs.append(f"missing_field: $.nodes.{ident}.state: unknown")
        if node.get("state") == "unsupported" and not isinstance(node.get("unsupported_reason"), str):
            errs.append(f"missing_field: $.nodes.{ident}.unsupported_reason: required")
        _ref_term(node.get("path_condition"), terms, "bool", f"$.nodes.{ident}.path_condition", errs)
        ir_state = node.get("ir_state")
        if isinstance(ir_state, dict):
            mem = ir_state.get("memory_id")
            if mem not in memories:
                errs.append(f"missing_ref: $.nodes.{ident}.ir_state.memory_id: {mem}")
            elif mem in recoverable:
                pass
            elif mem in explicit_mem and ir_state.get("memory_status") == "unsupported":
                pass
            else:
                errs.append(f"memory_not_recoverable: $.nodes.{ident}: memory {mem} is not recoverable")
        view = node.get("rocq_ebpf")
        if origin:
            if view is None:
                errs.append(f"rocq_null_on_origin: $.nodes.{ident}.rocq_ebpf: imported eBPF cannot omit R")
            elif isinstance(view, dict):
                _rocq(view, ident, errs)
        elif view is not None:
            errs.append(f"rocq_null_on_origin: $.nodes.{ident}.rocq_ebpf: no source map, view must be null")


def _rocq(view: dict[str, Any], ident: str, errs: list[str]) -> None:
    regs = view.get("regset")
    if not isinstance(regs, dict) or any(key not in regs for key in REG_KEYS):
        errs.append(f"ebpf_regs_incomplete: $.nodes.{ident}.rocq_ebpf.regset: need R0-R10, RAX, PC")
    frames = view.get("cstk")
    if not isinstance(frames, list):
        errs.append(f"ebpf_frame_incomplete: $.nodes.{ident}.rocq_ebpf.cstk: must be a list")
    else:
        for i, frame in enumerate(frames):
            if not isinstance(frame, dict) or any(key not in frame for key in FRAME_KEYS):
                errs.append(f"ebpf_frame_incomplete: $.nodes.{ident}.rocq_ebpf.cstk[{i}]: frame keys missing")
    for key in ("code_id", "tail_call_count", "mem"):
        if key not in view:
            errs.append(f"missing_field: $.nodes.{ident}.rocq_ebpf.{key}: required")


def _ref_term(ident: Any, terms: dict[str, dict[str, Any]], kind: str, path: str, errs: list[str]) -> None:
    if not isinstance(ident, str) or ident not in terms:
        errs.append(f"missing_ref: {path}: term {ident} missing")
        return
    got = terms[ident].get("sort", {}).get("kind")
    if got != kind:
        errs.append(f"guard_not_bool: {path}: sort {got}, want {kind}" if kind == "bool" else f"width_mismatch: {path}: sort {got}")


def _edges(items: Any, nodes: dict[str, dict[str, Any]], terms: dict[str, dict[str, Any]], errs: list[str]) -> None:
    if not isinstance(items, list):
        return
    for edge in items:
        if not isinstance(edge, dict) or not isinstance(edge.get("id"), str):
            continue
        ident = edge["id"]
        for key in ("from", "to", "kind", "guard", "ir_span", "events", "changed", "evidence_ids"):
            if key not in edge:
                errs.append(f"missing_field: $.edges.{ident}.{key}: required")
        if edge.get("from") not in nodes or edge.get("to") not in nodes:
            errs.append(f"missing_ref: $.edges.{ident}: endpoint missing")
        if edge.get("kind") not in EDGE_KINDS:
            errs.append(f"missing_field: $.edges.{ident}.kind: unknown")
        _ref_term(edge.get("guard"), terms, "bool", f"$.edges.{ident}.guard", errs)


def _coverage(doc: dict[str, Any], nodes: dict[str, dict[str, Any]], errs: list[str]) -> None:
    coverage = doc.get("coverage")
    if not isinstance(coverage, dict):
        errs.append("missing_field: $.coverage: must be an object")
        return
    for key in ("return_domain", "sink_domain", "assumptions", "frontier", "all_inputs_covered"):
        if key not in coverage:
            errs.append(f"missing_field: $.coverage.{key}: required")
    if coverage.get("all_inputs_covered") not in COVERED:
        errs.append("missing_field: $.coverage.all_inputs_covered: unknown")
    frontier = coverage.get("frontier")
    if not isinstance(frontier, list):
        errs.append("missing_field: $.coverage.frontier: must be a list")
        frontier = []
    for ident in frontier:
        if ident not in nodes:
            errs.append(f"missing_ref: $.coverage.frontier: node {ident} missing")
    bound = _is_bound(doc)
    if bound and not frontier:
        errs.append("frontier_mismatch: $.coverage.frontier: bound truncation needs a frontier")
    if not bound and frontier:
        errs.append("frontier_mismatch: $.coverage.frontier: frontier set without a bound truncation")
    if coverage.get("all_inputs_covered") == "established" and not _established_evidence(doc.get("evidence")):
        errs.append("established_without_evidence: $.coverage.all_inputs_covered: finished is not coverage")


def _is_bound(doc: dict[str, Any]) -> bool:
    run = doc.get("run")
    if isinstance(run, dict):
        truncation = run.get("truncation")
        if isinstance(truncation, dict) and truncation.get("kind") == "bound":
            return True
    for node in doc.get("nodes") or []:
        if isinstance(node, dict) and node.get("state") == "bound_truncated":
            return True
    for edge in doc.get("edges") or []:
        if isinstance(edge, dict) and edge.get("kind") == "boundary":
            return True
    return False


def _established_evidence(items: Any) -> bool:
    if not isinstance(items, list):
        return False
    for item in items:
        if not isinstance(item, dict):
            continue
        if item.get("kind") not in {"concrete_correspondence", "symbolic_correspondence"}:
            continue
        if item.get("status") not in {"checked", "proved"}:
            continue
        scope = item.get("scope")
        if isinstance(scope, list) and any(
            isinstance(entry, dict) and entry.get("kind") in {"node", "edge", "file"} and entry.get("id")
            for entry in scope
        ):
            return True
    return False


def _evidence_records(
    items: Any,
    nodes: dict[str, dict[str, Any]],
    edges: dict[str, dict[str, Any]],
    errs: list[str],
) -> None:
    if not isinstance(items, list):
        return
    for item in items:
        if not isinstance(item, dict) or not isinstance(item.get("id"), str):
            continue
        ident = item["id"]
        if item.get("kind") not in EVIDENCE_KINDS:
            errs.append(f"missing_field: $.evidence.{ident}.kind: unknown")
        scope = item.get("scope")
        if item.get("status") in {"checked", "proved"}:
            if not isinstance(scope, list) or not scope:
                errs.append(f"evidence_scope_global: $.evidence.{ident}: checked evidence needs a file, node, or edge scope")
            elif all(isinstance(entry, dict) and entry.get("kind") == "global" for entry in scope):
                errs.append(f"evidence_scope_global: $.evidence.{ident}: global scope is not coverage")
        if isinstance(scope, list):
            for entry in scope:
                if not isinstance(entry, dict):
                    continue
                target = entry.get("id")
                if entry.get("kind") == "node" and target not in nodes:
                    errs.append(f"missing_ref: $.evidence.{ident}: node {target} missing")
                if entry.get("kind") == "edge" and target not in edges:
                    errs.append(f"missing_ref: $.evidence.{ident}: edge {target} missing")


def _solver_fields(value: Any, path: str, errs: list[str]) -> None:
    if isinstance(value, dict):
        status = value.get("status") if "solver" in value or path.endswith("solver") or "smt" in path else None
        if isinstance(value.get("solver_status"), str):
            status = value["solver_status"]
        if isinstance(status, str) and status not in SOLVER:
            code = "solver_status_collapsed" if status in COLLAPSED or "unsat" in status and "unknown" in status else "missing_field"
            errs.append(f"{code}: {path}: solver status {status}")
        for key, child in value.items():
            _solver_fields(child, f"{path}.{key}", errs)
    elif isinstance(value, list):
        for i, child in enumerate(value):
            _solver_fields(child, f"{path}[{i}]", errs)


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: validate_state_graph.py <graph.json>", file=sys.stderr)
        return 2
    with open(argv[1], encoding="utf-8") as handle:
        doc = json.load(handle)
    errs = validate(doc)
    for err in errs:
        print(err)
    return 1 if errs else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
