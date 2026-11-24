"""Generate acceptance specs from the task evidence and pinned EXB2 host source."""

import argparse
from copy import deepcopy
import ctypes
import json
from pathlib import Path
import struct
import subprocess
import tempfile

from analysis import json_file

UPSTREAM = "ef1771d9c949771c707b93fd9da5c3e2602efee0"
EXB2 = ("noop", "prime", "log2", "copy", "fletcher32", "bsort", "strcmp")
MAX_SCALE = (0, 8192, 1024, 4096, 4096, 128, 4096)


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


def request(task, n, rounds):
    # Deterministic nonzero data and sentinels make accidental changes to
    # scratch, original input, and padding visible in the full packet check.
    variant = int(task == 2)
    patterned = bytes((i * 67 + 1) % 255 + 1 for i in range(4096))
    if task == 2:
        payload = b"".join(struct.pack("<Q", 1 << (i % 64)) for i in range(n))
    elif task == 5:
        payload = b"".join(struct.pack("<I", i) for i in range(n, 0, -1))
    elif task == 6:
        payload = (patterned[:n] + b"\0") * 2
    elif task in (3, 4):
        payload = patterned[:n]
    else:
        payload = b""
    scratch = len(payload) if task in (3, 5) else 0
    header = struct.pack("<4sHH14I", b"EXB2", 2, 64, task, n, rounds, variant,
                         19, len(payload), scratch, 0xffffffff, 0, 0, 0, 0, 0, 0)
    return (header + payload + b"\xa5" * scratch).ljust(8258, b"\xcc")


def independent_scratch(name, packet, output):
    if name not in ("copy", "bsort"):
        return
    n, = struct.unpack_from("<I", packet, 12)
    input_bytes, scratch = struct.unpack_from("<II", packet, 28)
    contents = packet[64:64 + input_bytes]
    if name == "bsort":
        values = sorted(word for word, in struct.iter_unpack("<I", contents))
        contents = struct.pack(f"<{len(values)}I", *values)
    if output[64 + input_bytes:64 + input_bytes + scratch] != contents:
        raise ValueError(f"independent {name} scratch check failed at n={n}")


def host_reference(upstream, name, build):
    library = build / f"{name}.so"
    subprocess.run(["cc", "-O2", "-shared", "-fPIC", "-DEB_HOST_ENTRY",
                    upstream / f"tests/xdp/{name}.c", "-o", library], check=True)
    entry = ctypes.CDLL(str(library)).exec_entry
    entry.argtypes = [ctypes.POINTER(ctypes.c_ubyte), ctypes.c_uint64]
    entry.restype = ctypes.c_uint64

    def expected(packet):
        buffer = (ctypes.c_ubyte * len(packet)).from_buffer_copy(packet)
        status = entry(buffer, len(packet))
        output = bytes(buffer)
        if status == 0:
            independent_scratch(name, packet, output)
        return {"action": 2 if status == 0 else 0, "bytes": patch(output, packet)}

    return expected


def exb2_cases(upstream, name, vector_path, build):
    task = EXB2.index(name)
    source = f"libbpf-mcu {UPSTREAM} tests/xdp/{name}.c built with EB_HOST_ENTRY"
    if name in ("copy", "bsort"):
        source += " and independently checked scratch bytes"
    host = host_reference(upstream, name, build)
    valid = (vector_path / "valid/input.bin").read_bytes()
    output = (vector_path / "valid/expected.bin").read_bytes()
    if host(valid) != {"action": 2, "bytes": patch(output, valid)}:
        raise ValueError(f"host reference disagrees with attachment for {name}")
    short = (vector_path / "short/input.bin").read_bytes()
    if len(short) != len(valid) - 1 or host(short) != {"action": 0, "bytes": {}}:
        raise ValueError(f"short fixture disagrees with EXB2 size contract for {name}")
    if name in ("noop", "copy", "bsort"):
        upstream_packet = (upstream / f"tests/fixtures/exb2/{name}.input.bin").read_bytes()
        upstream_expected = (upstream / f"tests/fixtures/exb2/{name}.expected.bin").read_bytes()
        if host(upstream_packet) != {"action": 2, "bytes": patch(upstream_expected, upstream_packet)}:
            raise ValueError(f"host reference disagrees with the upstream {name} vector")

    # Header validity ranges over the first magic byte. The full response,
    # including scratch and padding, is compared on each side.
    packet = request(task, min(4, MAX_SCALE[task]), 2)
    good = {"bytes": {"0": packet[0]}}
    invalid = bytes([0]) + packet[1:]
    cases = [case("magic-byte", packet, [
        {**host(packet), "when": good},
        {**host(invalid), "when": {"not": good}},
    ], source, symbolic_bytes=[0])]
    for name_, packet in (
        ("zero-scale", request(task, 0, 1)),
        ("first-scale", request(task, 1, 1)),
        ("scale-limit", request(task, MAX_SCALE[task], 1)),
        ("scale-over-limit", request(task, MAX_SCALE[task] + 1, 1)),
        ("zero-rounds", request(task, 0, 0)),
        ("rounds-over-limit", request(task, 0, 65537)),
    ):
        if task == 0 and name_ in ("first-scale", "scale-limit"):
            continue  # noop accepts only n=0 and has no inner loop
        cases.append(case(name_, packet, [host(packet)], source))
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence", type=Path, required=True)
    sources = parser.add_mutually_exclusive_group(required=True)
    sources.add_argument("--upstream", type=Path, help=f"historical checkout at {UPSTREAM}")
    sources.add_argument("--release-objects", action="store_true",
                         help="reuse the 23 original vectors and network specifications")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if args.release_objects:
        args.out.mkdir(parents=True)
        for name in sorted((*EXB2, "case_mark", "case_swap", "firewall", "just_drop", "just_tx")):
            paths = sorted((args.evidence / "vectors" / name).glob("*/expected.json"))
            if len(paths) != (1 if name == "just_drop" else 2):
                raise ValueError(f"missing original vector(s) for {name}")
            vectors = [vector(path.parent) for path in paths]
            cases = [] if name in EXB2 else network_cases(name, vectors)
            json_file(args.out / f"{name}.json", {"vectors": vectors, "cases": cases})
        return
    upstream = args.upstream.resolve()
    commit = subprocess.check_output(["git", "-C", upstream, "rev-parse", "HEAD"], text=True).strip()
    if commit != UPSTREAM:
        parser.error(f"expected upstream commit {UPSTREAM}, got {commit}")
    subprocess.run(["git", "-C", upstream, "diff", "--quiet", UPSTREAM, "--",
                    "tests/xdp", "tests/fixtures"], check=True)
    args.out.mkdir(parents=True)
    with tempfile.TemporaryDirectory(prefix="classifier-exb2-") as temp:
        for path in sorted((args.evidence / "vectors").iterdir()):
            name = path.name
            vectors = [vector(spec.parent) for spec in sorted(path.glob("*/expected.json"))]
            cases = (exb2_cases(upstream, name, path, Path(temp)) if name in EXB2 else
                     network_cases(name, vectors))
            json_file(args.out / f"{name}.json", {"vectors": vectors, "cases": cases})


if __name__ == "__main__":
    main()
