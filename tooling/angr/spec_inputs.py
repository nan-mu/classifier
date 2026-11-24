"""Translate saved vector inputs and independent expectations into specs."""

from copy import deepcopy
import json

EXB2 = ("noop", "prime", "log2", "copy", "fletcher32", "bsort", "strcmp")
NETWORK = ("case_mark", "case_swap", "firewall", "just_drop", "just_tx")
NEGATIVES = {"case_mark": "wrong-version", "case_swap": "wrong-version", "firewall": "wrong-count"}


def patch(expected, packet):
    if len(expected) != len(packet):
        raise ValueError("output packet length differs from input")
    return {str(i): after for i, (before, after) in enumerate(zip(packet, expected))
            if before != after}


def case(name, packet, expected, source, **input_fields):
    return {"id": name, "input": {"packet_hex": packet.hex(), **input_fields},
            "expect": expected, "source": source}


def fixture_spec(path):
    return json.loads((path / "expected.json").read_text())


def map_key(name, key):
    return {"map": name, "key": key}


def lookup(key, present):
    return {"helper": 1, **key, "present": present}


def vector(path):
    name = path.parent.name
    packet = (path / "input.bin").read_bytes()
    output = (path / "expected.bin").read_bytes()
    spec = fixture_spec(path)
    expected = {"action": spec["action"], "bytes": patch(output, packet)}
    source = f"task evidence vectors/{name}/{path.name} (expected.json and expected.bin)"
    if name in EXB2:
        producer = "pinned upstream byte fixture" if name in ("noop", "copy", "bsort") else (
            "same-source host reference")
        source += f" from {producer}"
    if spec["key"] is None:
        return case(path.name, packet, [expected], source)
    key = map_key({"firewall": "blacklist", "just_tx": "rxcnt"}[name], spec["key"])
    expected["helpers"] = [lookup(key, spec["hit"])]
    if spec["hit"]:
        expected["map"] = [{**key, "add": 1}]
    return case(path.name, packet, [expected], source,
                map=[{**key, "present": spec["hit"], "value": spec["old"]}])


def network_cases(name, vectors):
    by_id = {spec["id"]: spec for spec in vectors}
    if name == "just_drop":
        baseline = by_id["real-frame"]["input"]
        packet = bytes.fromhex(baseline["packet_hex"])
        return [case("drop", packet, [{"action": 1}], "minimal DROP contract",
                     lengths=[0, len(packet)], symbolic_bytes=[0, len(packet) - 1])]
    if name in ("case_mark", "case_swap"):
        baseline = by_id["matched"]
        packet = bytes.fromhex(baseline["input"]["packet_hex"])
        matched = {"length": 82, "bytes": {"74": 0}}
        expected = [{**baseline["expect"][0], "when": matched},
                    {"action": 2, "when": {"not": matched}}]
        good = case("version", packet, expected,
                    "CAS2 contract and matching frame from the task evidence",
                    lengths=[81, 82], symbolic_bytes=[74])
        bad = deepcopy(good)
        bad["id"] = "wrong-version"
        bad["expect"][0]["bytes"]["77"] = 3 - expected[0]["bytes"]["77"]
        return [good, bad]
    if name == "firewall":
        baseline = by_id["hash-True"]["input"]
        packet = bytes.fromhex(baseline["packet_hex"])
        key = map_key("blacklist", baseline["map"][0]["key"])
        if packet[26:30].hex() != key["key"]:
            raise ValueError("firewall evidence key does not match the IPv4 source")
        hit = {"when": {"present": [{**key, "is": True}]}, "action": 1,
               "helpers": [lookup(key, True)], "map": [{**key, "add": 1}]}
        miss = {"when": {"present": [{**key, "is": False}]}, "action": 2,
                "helpers": [lookup(key, False)]}
        good = case("blacklist", packet, [hit, miss], "firewall IPv4 blacklist contract",
                    map=[{**key, "present": None, "value": None}])
        bad = deepcopy(good)
        bad["id"] = "wrong-count"
        del bad["expect"][0]["map"]

        tracked = {"bytes": {"29": packet[29]}}
        variable_source = case("blacklist-source-byte", packet, [
            {**hit, "when": {"all": [tracked, hit["when"]]}},
            {**miss, "when": {"all": [tracked, miss["when"]]}},
            {"action": 2, "when": {"not": tracked},
             "helpers": [lookup(map_key("blacklist", {"packet_offset": 26}), False)]},
        ], "firewall IPv4 source byte and sparse blacklist contract",
            symbolic_bytes=[29], map=[{**key, "present": None, "value": None}])
        return [good, bad, variable_source]
    if name == "just_tx":
        baseline = by_id["tx+wrap"]["input"]
        packet = bytes.fromhex(baseline["packet_hex"])
        key = map_key("rxcnt", "11000000")
        mac_swap = packet[6:12] + packet[:6] + packet[12:]
        expected = {"action": 3, "bytes": patch(mac_swap, packet),
                    "helpers": [lookup(key, True)], "map": [{**key, "add": 1}]}
        return [case("tx-counter", packet, [expected], "JTX1 contract and evidence frame",
                     map=[{**key, "present": True, "value": None}])]
    raise ValueError(f"no network acceptance spec for {name}")
