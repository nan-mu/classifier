#!/usr/bin/env python3
"""Exercise the real Explorer and validate its exported objects (stdlib only)."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "contracts"))
from validate_state_graph import validate

HEADER = (ROOT / "alive2/tests/explore/loop.alive").read_text().split("define", 1)[0]


def check(condition, message):
    if not condition:
        raise AssertionError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--explorer", type=Path, required=True)
    parser.add_argument("--loader", type=Path, required=True)
    parser.add_argument("--corpus-out", type=Path, required=True)
    parser.add_argument("--out-dir", type=Path, required=True)
    args = parser.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    (args.out_dir / "test-report.json").unlink(missing_ok=True)
    results = []

    def run(name, program, inputs, unroll=1, extra=(), objects=None):
        folder = args.out_dir / name
        folder.mkdir(exist_ok=True)
        if isinstance(program, str):
            path = folder / "program.alive"
            path.write_text(HEADER + program)
        else:
            path = program
        initial = folder / "initial.json"
        initial.write_text(json.dumps({"inputs": inputs, **({"objects": objects} if objects is not None else {})}))
        graph = folder / "graph.json"
        command = [str(args.explorer), "run", str(path), "--initial", str(initial), "--unroll", str(unroll), "--graph-out", str(graph), *map(str, extra)]
        execution = subprocess.run(command, text=True, capture_output=True, timeout=45)
        check(execution.returncode == 0, f"{name}: exit {execution.returncode}: {execution.stderr}")
        doc = json.loads(graph.read_text())
        errors = validate(doc)
        check(not errors, f"{name}: validator: {errors[:10]}")
        check(doc["program"]["ir_hash"] == digest(path), f"{name}: incorrect IR digest")
        check(doc["run"]["initial_id"] == digest(initial), f"{name}: incorrect initial digest")
        check(doc["coverage"]["all_inputs_covered"] == "not_established", "test is not a symbolic proof")
        check(all(node["rocq_ebpf"] is None for node in doc["nodes"]), "unexpected Rocq claim")
        results.append({"name": name, "status": "passed", "nodes": len(doc["nodes"]), "terms": len(doc["terms"]), "graph": str(graph.relative_to(args.out_dir)), "sha256": digest(graph), "truncation": doc["run"]["truncation"]["kind"]})
        return doc

    def terms(doc):
        return {term["id"]: term for term in doc["terms"]}

    def binding(kind, value=None, name="%x", ty="i64"):
        return {"name": name, "type": ty, "kind": kind, **({"value": str(value)} if value is not None else {})}

    def exits(doc):
        index = terms(doc)
        return [int(index[value["value"]]["digits"]) for n in doc["nodes"] if n["state"] == "exit" for value in n["ir_state"]["returned_values"]]

    branch = """define i64 @branch(i64 %x) memory(none) {
entry:
  %c = icmp eq i64 %x, 0
  br i1 %c, label %yes, label %no
yes:
  ret i64 7
no:
  ret i64 9
}
"""
    zero = run("concrete-zero", branch, [binding("concrete", 0)])
    one = run("concrete-one", branch, [binding("concrete", 1)])
    check(exits(zero) == [7] and exits(one) == [9], "concrete input did not affect execution")
    check(zero["run"]["id"] != one["run"]["id"], "run ID omitted initial state")
    symbolic = run("symbolic-branch", branch, [binding("symbolic")])
    check({e["kind"] for e in symbolic["edges"]} >= {"taken", "not_taken"}, "symbolic branch lost an edge")
    check(any(terms(symbolic)[n["path_condition"]]["op"] != "true" for n in symbolic["nodes"]), "path conditions were replaced by true")
    again = run("symbolic-repeat", branch, [binding("symbolic")])
    check(symbolic["terms"] == again["terms"], "expression IDs are not repeatable")
    run("undefined", branch, [binding("undefined")])
    poison = run("poison", branch, [binding("poison")])
    check(any(n["state"] == "ub" for n in poison["nodes"]), "poison branch must expose UB")

    nested = run("nested", """define i64 @nested(i64 %x) memory(none) {
entry:
  %a = icmp eq i64 %x, 0
  br i1 %a, label %left, label %right
left:
  %b = icmp eq i64 %x, 1
  br i1 %b, label %contradiction, label %other
contradiction:
  ret i64 2
other:
  ret i64 3
right:
  ret i64 4
}
""", [binding("symbolic")])
    index = terms(nested)
    def descendants(ident, seen=None):
        seen = set() if seen is None else seen
        if ident not in seen:
            seen.add(ident)
            for arg in index[ident]["args"]:
                descendants(arg, seen)
        return seen
    for node in nested["nodes"]:
        if node["location"]["block"] == "%contradiction":
            ops = [index[ref]["op"] for ref in descendants(node["path_condition"])]
            check("and" in ops and ops.count("eq") >= 2, "nested path dropped its predecessor condition")

    phi = run("phi-terms", """define i64 @phi(i64 %x, i8 %y) memory(none) {
entry:
  %a = add i64 %x, 1
  %a2 = add i64 %x, 1
  %b = sub i64 %a, 3
  %m = mul i64 %b, 7
  %bits = xor i64 %m, 19
  %mask = and i64 %bits, 255
  %wide = zext i8 %y to i64
  %c = icmp ult i64 %x, %wide
  br i1 %c, label %left, label %right
left:
  br label %join
right:
  br label %join
join:
  %p = phi i64 [ %mask, %left ], [ %wide, %right ]
  ret i64 %p
}
""", [binding("symbolic"), binding("symbolic", name="%y", ty="i8")])
    ops = {t["op"] for t in phi["terms"]}
    # Z3 rewrites subtract-by-constant to addition, masks to extracts, and
    # names its ITE declaration "if". Inspect the actual native AST.
    check(ops >= {"bvadd", "bvmul", "bvxor", "extract", "if"}, f"missing native DAG operators: {ops}")
    final = phi["nodes"][-1]
    bindings = {v["instr"]: v for v in final["ir_state"]["values"]}
    check(bindings["%a"]["term"] == bindings["%a2"]["term"], "equal expressions were not deduplicated")
    check({t["sort"].get("width") for t in phi["terms"]} >= {8, 64}, "integer widths lost")

    loop_path = ROOT / "alive2/tests/explore/loop.alive"
    complete = run("loop-return", loop_path, [], 4)
    cutoff = run("loop-boundary", loop_path, [], 1)
    check(exits(complete) == [3] and complete["run"]["truncation"]["kind"] == "none", "completed loop was truncated")
    check(cutoff["run"]["truncation"]["kind"] == "bound" and any(e["kind"] == "boundary" for e in cutoff["edges"]), "loop boundary was lost")
    check(max(n["unroll"] for n in complete["nodes"]) >= 2, "unroll instance missing")
    resource = run("step-budget", loop_path, [], 4, ["--budget-steps", "2"])
    check(resource["run"]["truncation"]["kind"] == "resource", "instruction budget mislabeled")
    memory = run("pointer-memory", ROOT / "alive2/tests/explore/load.alive", [binding("symbolic", name="%p", ty="ptr")])
    check(any(m["blocks"] for m in memory["memories"]), "symbolic memory arrays omitted")

    for name in ("just_drop", "firewall", "helper_loop", "xdp_drop"):
        program = args.corpus_out / name / (name + ".alive")
        inspected = subprocess.run([str(args.loader), "--inspect", str(program)], capture_output=True, text=True, check=True).stdout
        inputs = [binding("symbolic", name=row.split()[1], ty=row.split()[2]) for row in inspected.splitlines() if row.startswith("in ")]
        origin = program.with_suffix(".origin.json")
        doc = run(name, program, inputs, 2, ["--origin", origin])
        check(doc["program"]["origin"]["sha256"] == digest(origin), "origin hash lost")
        check(any(n["origin_location"] is not None for n in doc["nodes"]), "original SSA origins not imported")
        if name == "helper_loop":
            check(doc["run"]["truncation"]["kind"] == "bound", "real loop lost its backedge boundary")

    # Negative cases use a fresh target and must never publish partial graphs.
    bad_dir = args.out_dir / "rejected"
    bad_dir.mkdir(exist_ok=True)
    bad_initial = bad_dir / "initial.json"
    for label, text, extra, error in [
        ("objects", json.dumps({"inputs":[binding("symbolic")], "objects": []}), [], "INITIAL_STATE_UNSUPPORTED"),
        ("type", json.dumps({"inputs":[binding("symbolic", ty="i32")]}), [], "type mismatch"),
        ("duplicate", json.dumps({"inputs":[binding("symbolic"), binding("symbolic")]}), [], "duplicate input"),
        ("missing", '{"inputs":[]}', [], "missing input"),
        ("malformed", "{", [], "invalid JSON"),
        ("range", json.dumps({"inputs":[binding("concrete", "18446744073709551616")]}), [], "stoull"),
        ("trailing", '{"inputs":[]} true', [], "JSON"),
        ("unroll", '{"inputs":[]}', ["--unroll", "1junk"], "positive integer"),
        ("environment", '{"inputs":[]}', ["--environment", bad_dir / "env.json"], "ENVIRONMENT_UNSUPPORTED"),
    ]:
        bad_initial.write_text(text)
        graph = bad_dir / (label + ".json")
        result = subprocess.run([str(args.explorer), "run", str(args.out_dir / "concrete-zero/program.alive"), "--initial", str(bad_initial), "--unroll", "1", "--graph-out", str(graph), *map(str, extra)], capture_output=True, text=True)
        check(result.returncode != 0 and error in result.stderr, f"{label}: unexpected rejection: {result.stderr}")
        check(not graph.exists() and not list(bad_dir.glob(label + ".json.tmp.*")), f"{label}: partial graph left behind")
        results.append({"name": "reject-" + label, "status": "passed", "diagnostic": result.stderr.strip()})
    for label, mutation in [
        ("duplicate-node", lambda d: d["nodes"].append(copy.deepcopy(d["nodes"][0]))),
        ("missing-edge-target", lambda d: d["edges"][0].update(to="missing-node")),
        ("term-cycle", lambda d: d["terms"][0].update(args=[d["terms"][0]["id"]])),
        ("guard-width", lambda d: next(t for t in d["terms"] if t["id"] == d["edges"][0]["guard"]).update(sort={"kind":"bv", "width":1})),
    ]:
        corrupted = copy.deepcopy(symbolic)
        mutation(corrupted)
        check(bool(validate(corrupted)), f"validator accepted {label} in actual Explorer output")
        results.append({"name":"validator-" + label, "status":"passed"})
    report = {"evidence_kind":"test", "scope":"native Explorer output and structural validation; no source-state or symbolic correspondence proof", "explorer_sha256":digest(args.explorer), "results":results, "rocq_correspondence":"not_implemented", "initial_memory_objects":"unsupported"}
    (args.out_dir / "test-report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"{len(results)} Explorer cases passed; {args.out_dir / 'test-report.json'}")


if __name__ == "__main__":
    main()
