"""Input domains, observational specifications, and replayable SMT queries."""

from dataclasses import asdict, dataclass
import json
from pathlib import Path
import platform

import z3

from machine import (
    CONTEXT, CONTEXT_BYTES, FRAME, PACKET, Entry, Machine, State, bv, literal,
    octets, resize, solver_gap, unpack,
)


@dataclass(frozen=True)
class Limits:
    max_steps: int
    max_back_edges: int
    max_paths: int
    timeout_ms: int


def json_file(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def expression(value):
    value = z3.simplify(value)
    if z3.is_true(value):
        return True
    if z3.is_false(value):
        return False
    return literal(value) if z3.is_bv_value(value) else value.sexpr()


def describe(value):
    if isinstance(value, z3.ExprRef):
        return expression(value)
    if isinstance(value, list):
        return [describe(item) for item in value]
    if isinstance(value, dict):
        return {key: describe(item) for key, item in value.items()}
    return value


def packet_bytes(data):
    values = [literal(byte) for byte in data]
    if None not in values:
        return {"hex": bytes(values).hex()}
    return {"bytes": [expression(byte) for byte in data]}


def fields(data, required, optional=()):
    if not isinstance(data, dict) or not required <= data.keys():
        raise ValueError(f"expected object with fields {sorted(required)}")
    extra = data.keys() - required - set(optional)
    if extra:
        raise ValueError(f"unrecognized fields: {sorted(extra)}")


def uint(value, bound, label):
    if type(value) is not int or not 0 <= value < bound:
        raise ValueError(f"{label} must be an integer in 0..{bound - 1}")
    return value


def offset(value, bound):
    if not isinstance(value, str) or not value.isdecimal():
        raise ValueError(f"invalid byte offset {value!r}")
    return uint(int(value), bound, "offset")


def boolean(value):
    if type(value) is not bool:
        raise ValueError("expected a boolean")
    return value


class Domain:
    def __init__(self, case, maps):
        fields(case, {"id", "input"}, ("expect", "vectors", "source"))
        self.case = case
        self.maps = {m.name: m for m in maps}
        config = case["input"]
        fields(config, {"packet_hex"}, ("lengths", "symbolic_bytes", "map", "context_hex"))
        data = bytes.fromhex(config["packet_hex"])
        if len(data) >= FRAME - PACKET - 512:
            raise ValueError("packet template overlaps stack region")
        self.packet = [bv(byte, 8) for byte in data]
        lengths = sorted(set(uint(length, len(data) + 1, "length")
                             for length in config.get("lengths", [len(data)])))
        self.length = bv(lengths[0], 32) if len(lengths) == 1 else z3.BitVec("length", 32)
        preconditions = [z3.Or(*(self.length == length for length in lengths))]
        for index in config.get("symbolic_bytes", []):
            uint(index, len(data), "symbolic byte offset")
            self.packet[index] = z3.BitVec(f"packet_{index}", 8)

        tail = bytes.fromhex(config.get("context_hex", "00" * (CONTEXT_BYTES - 8)))
        if len(tail) != CONTEXT_BYTES - 8:
            raise ValueError("context_hex must contain 16 bytes after data and data_end")
        self.context = (octets(bv(PACKET, 32), 4)
                        + octets(bv(PACKET, 32) + self.length, 4)
                        + [bv(byte, 8) for byte in tail])
        self.entries = {}
        for item in config.get("map", []):
            fields(item, {"map", "key", "present", "value"})
            identity = self.identity(item)
            map_ = self.maps[identity[0]]
            default = map_.default(identity[1])
            if identity in self.entries:
                raise ValueError(f"duplicate map/key {identity}")
            name = f"map_{len(self.entries)}"
            bits = map_.value_bytes * 8
            value = item["value"]
            value = z3.BitVec(name + "_value", bits) if value is None else bv(
                uint(value, 1 << bits, "initial map value"), bits
            )
            present = item["present"]
            present = z3.Bool(name + "_present") if present is None else z3.BoolVal(boolean(present))
            if map_.array:
                if z3.is_false(default.present):
                    raise ValueError(f"array key out of bounds: {identity}")
                preconditions.append(present)
            self.entries[identity] = Entry(present, value)

        for map_ in maps:
            if not map_.array:
                entries = [entry.present for identity, entry in self.entries.items()
                           if identity[0] == map_.name]
                if len(entries) > map_.capacity:
                    preconditions.append(z3.PbLe([(present, 1) for present in entries], map_.capacity))
        self.guard = z3.simplify(z3.And(*preconditions))

    def identity(self, item):
        map_ = self.maps.get(item["map"])
        if map_ is None:
            raise ValueError(f"unknown map {item['map']!r}")
        key = bytes.fromhex(item["key"])
        if len(key) != map_.key_bytes:
            raise ValueError(f"wrong key width for {map_.name}")
        return map_.name, key.hex()

    def initial(self):
        regs = [None] * 11
        regs[1], regs[10] = bv(CONTEXT, 64), bv(FRAME, 64)
        return State(self.packet.copy(), self.length, self.context.copy(), regs,
                     self.entries.copy(), self.guard)

    def entry(self, identity):
        return self.entries.get(identity, self.maps[identity[0]].default(identity[1]))

    def when(self, predicates):
        fields(predicates, set(), ("length", "bytes", "present", "not", "all"))
        clauses = []
        if "length" in predicates:
            length = uint(predicates["length"], len(self.packet) + 1, "length")
            clauses.append(self.length == length)
        for index, value in predicates.get("bytes", {}).items():
            index = offset(index, len(self.packet))
            clauses.append(self.packet[index] == uint(value, 256, "packet byte"))
        for item in predicates.get("present", []):
            fields(item, {"map", "key", "is"})
            actual = self.entry(self.identity(item)).present
            clauses.append(actual == boolean(item["is"]))
        if "not" in predicates:
            clauses.append(z3.Not(self.when(predicates["not"])))
        clauses.extend(self.when(predicate) for predicate in predicates.get("all", []))
        return z3.simplify(z3.And(*clauses))

    def replay_input(self, model):
        def evaluate(expr):
            return expression(model.eval(expr, model_completion=True))

        # Keep the original backing template so expectation offsets continue
        # to refer to the same bytes even when the model selects a short frame.
        return {
            "packet_hex": bytes(evaluate(byte) for byte in self.packet).hex(),
            "lengths": [evaluate(self.length)],
            "context_hex": bytes(evaluate(byte) for byte in self.context[8:]).hex(),
            "map": [{"map": name, "key": key, "present": evaluate(entry.present),
                     "value": evaluate(entry.value)}
                    for (name, key), entry in sorted(self.entries.items())],
        }


class Expectation:
    def __init__(self, domain, spec):
        fields(spec, {"action"}, ("when", "bytes", "context", "map", "helpers"))
        self.when = domain.when(spec.get("when", {}))
        self.action = uint(spec["action"], 1 << 32, "XDP action")
        self.packet = domain.packet.copy()
        self.context = domain.context.copy()
        for index, value in spec.get("bytes", {}).items():
            self.packet[offset(index, len(self.packet))] = bv(uint(value, 256, "packet byte"), 8)
        for index, value in spec.get("context", {}).items():
            self.context[offset(index, len(self.context))] = bv(uint(value, 256, "context byte"), 8)
        self.entries = {}
        for item in spec.get("map", []):
            fields(item, {"map", "key"}, ("present", "value", "add"))
            identity = domain.identity(item)
            if identity in self.entries or "value" in item and "add" in item:
                raise ValueError(f"ambiguous expected map entry {identity}")
            initial = domain.entry(identity)
            bits = initial.value.size()
            value = initial.value
            if "add" in item:
                value += uint(item["add"], 1 << bits, "map increment")
            if "value" in item:
                value = bv(uint(item["value"], 1 << bits, "map value"), bits)
            present = initial.present
            if "present" in item:
                present = z3.BoolVal(boolean(item["present"]))
            self.entries[identity] = Entry(present, value)

        self.helpers = []
        for item in spec.get("helpers", []):
            fields(item, {"helper", "map", "key", "present"})
            name = item["map"]
            map_ = domain.maps.get(name)
            if map_ is None:
                raise ValueError(f"unknown map {name!r}")
            if isinstance(item["key"], dict):
                fields(item["key"], {"packet_offset"})
                start = uint(item["key"]["packet_offset"],
                             len(domain.packet) - map_.key_bytes + 1, "packet key offset")
                key = unpack(domain.packet[start:start + map_.key_bytes])
            else:
                _, key_hex = domain.identity(item)
                key = bv(int.from_bytes(bytes.fromhex(key_hex), "little"), map_.key_bytes * 8)
            self.helpers.append((uint(item["helper"], 1 << 32, "helper ID"),
                                 name, key, boolean(item["present"])))

    def conditions(self, domain, state):
        action = resize(state.regs[0], 32)
        checks = {"action": (action == self.action, action, self.action)}
        start, end = unpack(self.context[:4]), unpack(self.context[4:8])
        for index, (actual, expected) in enumerate(zip(state.packet, self.packet)):
            if not actual.eq(expected):
                at = PACKET + index
                checks[f"packet[{index}]"] = (
                    z3.Implies(z3.And(z3.ULE(start, at), z3.ULT(bv(at, 32), end)),
                               actual == expected), actual, expected
                )
        checks.update({f"context[{index}]": (actual == expected, actual, expected)
                       for index, (actual, expected) in enumerate(zip(state.context, self.context))
                       if not actual.eq(expected)})

        for identity in domain.entries.keys() | self.entries.keys() | state.maps.keys():
            initial = domain.entry(identity)
            expected = self.entries.get(identity, initial)
            actual = state.maps.get(identity, initial)
            name, key = identity
            checks[f"{name}[{key}].present"] = (
                actual.present == expected.present, actual.present, expected.present
            )
            checks[f"{name}[{key}].value"] = (
                z3.Implies(expected.present, actual.value == expected.value), actual.value, expected.value
            )

        events = [event for event in state.events if event["kind"] == "helper"]
        checks["helper count"] = (z3.BoolVal(len(events) == len(self.helpers)),
                                  len(events), len(self.helpers))
        for index, (event, expected) in enumerate(zip(events, self.helpers)):
            helper, name, key, present = expected
            for field, actual, expected in (
                ("id", event["helper"], helper), ("map", event["map"], name),
                ("key", event["key_value"], key), ("present", event["present"], present),
            ):
                checks[f"helper[{index}].{field}"] = (actual == expected, actual, expected)
        return checks


def observation(state):
    start = z3.simplify(unpack(state.context[:4]) - PACKET)
    end = z3.simplify(unpack(state.context[4:8]) - PACKET)
    lo, hi = literal(start), literal(end)
    if lo is not None and hi is not None:
        buffer = packet_bytes(state.packet[lo:hi])
        buffer["origin"] = lo
    else:
        buffer = packet_bytes(state.packet)
        buffer["origin"] = 0
    return describe({
        "guard": state.guard,
        "exit_pc": state.pc,
        "steps": state.steps,
        "back_edges": state.back_edges,
        "action": resize(state.regs[0], 32),
        "packet_range": {"start": start, "end": end},
        "packet": buffer,
        "context": packet_bytes(state.context),
        "map": [{"map": name, "key": key, "present": entry.present, "value": entry.value}
                for (name, key), entry in sorted(state.maps.items())],
        "events": state.events,
    })


def query(out, name, predicate, timeout):
    solver = z3.Solver()
    solver.set(timeout=timeout)
    solver.add(z3.simplify(predicate))
    path = name + ".smt2"
    (out / path).write_text(f"(set-option :timeout {timeout})\n" + solver.to_smt2())
    result = solver.check()
    info = {"status": str(result), "smtlib": path}
    if result == z3.sat:
        return info, solver.model()
    if result == z3.unknown:
        info["reason"] = solver.reason_unknown()
        info["kind"] = solver_gap(info["reason"])
    return info, None


def execute(program, domain, limits):
    machine = Machine(program.instructions, program.maps, limits.max_steps, limits.max_back_edges,
                      limits.max_paths, limits.timeout_ms)
    return machine.run(domain.initial())


def compare(domain, state, expects):
    clauses = {}
    for i, expected in enumerate(expects):
        for label, (predicate, actual, desired) in expected.conditions(domain, state).items():
            clauses[f"{i}: {label}"] = (z3.Implies(expected.when, predicate), actual, desired)
    return clauses


def run_case(program, case, out, limits):
    domain = Domain(case, program.maps)
    expect = case.get("expect")
    if expect is not None and (not isinstance(expect, list) or not expect):
        raise ValueError("expect must be a nonempty list")
    expects = [Expectation(domain, spec) for spec in expect or []]
    out.mkdir()
    nonempty, _ = query(out, "domain", domain.guard, limits.timeout_ms)
    report = {"id": case["id"], "source": case.get("source"), "domain": nonempty,
              "precondition": expression(domain.guard), "comparison": "not_requested",
              "exits": [], "unresolved": []}
    if nonempty["status"] != "sat":
        report["verdict"] = "empty_domain" if nonempty["status"] == "unsat" else "undetermined"
        json_file(out / "result.json", report)
        return report

    exits, gaps = execute(program, domain, limits)
    cover = z3.Or(*(state.guard for state in exits))
    coverage, missing = query(out, "uncovered", z3.And(domain.guard, z3.Not(cover)), limits.timeout_ms)
    report.update(coverage=coverage, exits=[observation(state) for state in exits],
                  unresolved=describe(gaps))
    if missing is not None:
        report["uncovered_input"] = domain.replay_input(missing)
    report["verdict"] = "covered" if coverage["status"] == "unsat" else "undetermined"

    if expects:
        spec_uncovered, unspecified = query(
            out, "spec-uncovered",
            z3.And(domain.guard, z3.Not(z3.Or(*(expected.when for expected in expects)))),
            limits.timeout_ms,
        )
        report["spec_coverage"] = spec_uncovered
        if unspecified is not None:
            report["unspecified_input"] = domain.replay_input(unspecified)
        comparisons = [compare(domain, state, expects) for state in exits]
        failures = [z3.And(state.guard, z3.Not(z3.And(*(item[0] for item in clauses.values()))))
                    for state, clauses in zip(exits, comparisons)]
        result, model = query(out, "negated-spec", z3.And(domain.guard, z3.Or(*failures)),
                              limits.timeout_ms)
        report["comparison"] = result
        if model is not None:
            counterexample = {**case, "input": domain.replay_input(model)}
            case_path = out / "counterexample.json"
            json_file(case_path, {"cases": [counterexample]})
            replay_domain = Domain(counterexample, program.maps)
            states, _ = execute(program, replay_domain, limits)
            replay_expects = [Expectation(replay_domain, spec) for spec in expect]
            differences = [
                {"field": label, "observed": describe(actual), "expected": describe(expected)}
                for state in states for label, (predicate, actual, expected)
                in compare(replay_domain, state, replay_expects).items()
                if z3.is_false(z3.simplify(predicate))
            ]
            report["counterexample"] = {
                "input": counterexample["input"], "spec": case_path.name,
                "differences": differences, "replayed": bool(differences),
                "observed": [observation(state) for state in states],
            }
            report["verdict"] = "counterexample" if differences else "undetermined"
        elif coverage["status"] == result["status"] == spec_uncovered["status"] == "unsat":
            report["verdict"] = "holds"
        else:
            report["verdict"] = "undetermined"
    json_file(out / "result.json", report)
    return report


def analyze_program(program, document, out, limits, selection):
    fields(document, set(), ("cases", "vectors"))
    report = {"program": program.name, "container_sha256": program.digest,
              "engine": "ebpf", "engine_selection": selection,
              "image_sha256": program.image_digest, "maps": [asdict(m) for m in program.maps],
              "limits": asdict(limits), "tools": {"python": platform.python_version(),
                                                  "z3": z3.get_version_string()},
              "vectors": [], "cases": []}
    json_file(out / "spec.json", document)
    for group in ("vectors", "cases"):
        cases = document.get(group, [])
        if not isinstance(cases, list) or any(not isinstance(case, dict) for case in cases):
            raise ValueError(f"{group} must be an array of objects")
        directory = out / group
        directory.mkdir()
        identifiers = set()
        for case in cases:
            name = case.get("id")
            if (not isinstance(name, str) or not name or name in {".", ".."}
                    or any(c not in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_+-"
                           for c in name) or name in identifiers):
                raise ValueError(f"invalid or duplicate case id: {name!r}")
            identifiers.add(name)
            if group == "vectors":
                if not case.get("expect"):
                    raise ValueError("a concrete vector requires expected observations")
                domain = Domain(case, program.maps)
                if (literal(domain.length) is None or any(literal(b) is None for b in domain.packet)
                        or any(literal(e.value) is None or not (z3.is_true(e.present)
                               or z3.is_false(e.present)) for e in domain.entries.values())):
                    raise ValueError("a concrete vector has symbolic inputs")
            result = run_case(program, case, directory / name, limits)
            report[group].append({"id": name, "verdict": result["verdict"],
                                  "paths": len(result["exits"]),
                                  "result": f"{group}/{name}/result.json"})

    vectors = report["vectors"]
    report["concrete_counts"] = {"passed": sum(row["verdict"] == "holds" for row in vectors),
                                 "total": len(vectors)}
    json_file(out / "result.json", report)
    return report
