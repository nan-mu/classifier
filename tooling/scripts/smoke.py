import argparse
import base64
import json
import os
from pathlib import Path
import signal
import socket
import subprocess
import tempfile
import time
import urllib.error
import urllib.request

from dev import stop_processes


def request(base, method, path, body=None):
    data = None if body is None else json.dumps(body).encode()
    req = urllib.request.Request(
        base + path, data=data, method=method,
        headers={"Content-Type": "application/json"},
    )
    with urllib.request.urlopen(req, timeout=120) as response:
        chunks = []
        while True:
            chunk = response.read(64 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
        payload = b"".join(chunks)
        declared_length = response.headers.get("Content-Length")
        if declared_length is not None:
            assert len(payload) == int(declared_length), (
                f"HTTP response truncated: got {len(payload)}, expected {declared_length} bytes"
            )
        return json.loads(payload)


def snapshots(base):
    result = {}
    for budget in (3, 2):
        created = request(base, "POST", "/api/session", {"budget": budget, "arch": "rv32imc"})
        assert created["arch"] == "rv32imc", created["arch"]
        assert created["program"] == "just_tx.elf", created["program"]
        path = "/api/session/" + created["id"]
        stepped = request(base, "POST", path + "/step", {})
        done = request(base, "POST", path + "/run", {})
        assert request(base, "GET", path) == done, "GET must return the final snapshot"
        assert done["status"] == "fail", (budget, done["status"])
        assert done["reason"] == "LimitExceeded", done["reason"]
        assert done["failed"] is None, "budget exhaustion does not reject a step"
        assert len(stepped["nodes"]) > len(created["nodes"]), "step must expand the graph"
        result[f"just_tx.elf/{budget}"] = [created, stepped, done]
    created = request(base, "POST", "/api/session", {"budget": 512})
    path = "/api/session/" + created["id"]
    done = request(base, "POST", path + "/run", {})
    assert done["status"] == "fail", done["status"]
    assert done["reason"] == "LimitExceeded", done["reason"]
    assert done["failed"] is None, "all instructions before budget exhaustion must succeed"
    assert done["focus"] == 521 and done["cursor_j"] == 75
    assert done["fuel"] == 0 and len(done["work"]) == 30
    assert done["work"][0] == done["focus"]
    assert len(done["nodes"]) == 552 and len(done["edges"]) == 551
    assert all(e["from"] not in done["work"] for e in done["edges"])
    assert sum(n["loc"] == "exit" for n in done["nodes"]) == 10
    after_load = next(n for n in done["nodes"] if n["id"] == 263)
    assert after_load["loc"] == "50"
    assert any(e["from"] == 244 and e["to"] == 263 for e in done["edges"])
    assert any(e["reg"] == "real32:13" and e["term"] == "externalResult166_2(1)"
               for e in after_load["exprs"]), "second Map word must have been loaded"
    assert any(e["reg"] == "map32:14539" and e["term"] == "externalResult166_2(1)"
               for e in after_load["exprs"]), "untouched second word must materialize"
    assert any(
        n["loc"] == "55"
        and any(e["reg"] == "map32:13861" and e["term"] == "add32(regVar166(real32:10),1)"
                for e in n["exprs"])
        and any(e["reg"] == "map32:14539" and e["term"].startswith("add32(externalResult166_2(1),")
                for e in n["exprs"])
        for n in done["nodes"]
    ), "both Map stores must update the words that were loaded"
    assert any(
        p.get("kind") == "helper" and p.get("helperId") == 1
        for n in done["nodes"]
        for p in n["predicates"]
    ), "lookup helper Predicate must appear in the graph"
    assert any(
        e["reg"].startswith("map32:") and e["term"].startswith("regVar")
        for n in done["nodes"]
        for e in n["exprs"]
    ), "lookup must introduce mapWord = regVar(a0)"
    assert any(
        e["reg"].startswith("packet32:")
        for n in done["nodes"]
        for e in n["exprs"]
    ), "packet bytes must appear in the just_tx graph"
    assert request(base, "GET", path) == done, "GET must return the final snapshot"
    fixtures = Path(__file__).resolve().parents[1] / "fixtures"
    default_elf = (fixtures / "just_tx.elf").read_bytes()
    uploaded = request(
        base,
        "POST",
        "/api/session",
        {"image_b64": base64.b64encode(default_elf).decode(), "name": "upload.elf"},
    )
    assert uploaded["program"] == "upload.elf"
    assert uploaded["nodes"] == created["nodes"]
    firewall = (fixtures / "xdp.elf").read_bytes()
    fw = request(
        base,
        "POST",
        "/api/session",
        {"image_b64": base64.b64encode(firewall).decode(), "name": "xdp.elf", "budget": 512},
    )
    fw_done = request(base, "POST", "/api/session/" + fw["id"] + "/run", {})
    assert fw_done["status"] == "complete", fw_done["reason"]
    assert fw_done["failed"] is None
    assert any(
        e["reg"] == "real32:10" and "externalResult" in e["term"]
        for n in fw_done["nodes"] for e in n["exprs"]
    ), "helper effects must reach the graph"
    assert any(
        p.get("kind") == "helper" and p.get("helperId") is not None
        for n in fw_done["nodes"]
        for p in n["predicates"]
    ), "firewall paths must carry helper Predicates"
    assert any(
        p.get("kind") == "ret" for n in fw_done["nodes"] for p in n["predicates"]
    ), "Exit must observe a ret Predicate"
    assert any(
        p.get("kind") == "cmp" and p.get("rel") == "ltu"
        for n in fw_done["nodes"] for p in n["predicates"]
    ), "branch cmp Predicates must appear"
    assert {"taken", "not_taken"} <= {e["dir"] for e in fw_done["edges"]}
    invalid = [
        default_elf[:-1],
        default_elf + b"x",
        b"\x13\0\0\0",
        default_elf[:-1] + bytes([default_elf[-1] ^ 1]),
    ]
    for payload in invalid:
        try:
            request(base, "POST", "/api/session", {"image_b64": base64.b64encode(payload).decode()})
        except urllib.error.HTTPError as error:
            assert error.code == 400, error.code
        else:
            raise AssertionError("invalid compact ELF must return HTTP 400")
    result["just_tx.elf/512"] = [created, done]
    result["xdp.elf/512"] = [fw, fw_done]
    try:
        request(base, "GET", "/api/session/missing")
    except urllib.error.HTTPError as error:
        assert error.code == 404, error.code
    else:
        raise AssertionError("missing session must return HTTP 404")
    return result


def main():
    parser = argparse.ArgumentParser(description="Check live session API behavior and compare migration snapshots.")
    parser.add_argument("--server", type=Path, required=True)
    parser.add_argument("--parent-pid", type=int, default=os.getppid())
    parser.add_argument("--capture", type=Path)
    parser.add_argument("--compare", type=Path)
    args = parser.parse_args()
    stopped = False

    def interrupted(_signum, _frame):
        nonlocal stopped
        stopped = True

    signal.signal(signal.SIGHUP, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    signal.signal(signal.SIGTERM, interrupted)
    with socket.socket() as sock:
        sock.bind(("127.0.0.1", 0))
        port = sock.getsockname()[1]
    base = f"http://127.0.0.1:{port}"
    with tempfile.TemporaryFile(mode="w+") as log:
        server = subprocess.Popen(
            [str(args.server.resolve())],
            env={**os.environ, "PORT": str(port)}, stdout=log, stderr=log, start_new_session=True,
        )
        try:
            deadline = time.monotonic() + 30
            while True:
                if stopped or os.getppid() != args.parent_pid:
                    raise KeyboardInterrupt
                if server.poll() is not None:
                    raise RuntimeError("server exited before listening")
                try:
                    with socket.create_connection(("127.0.0.1", port), timeout=1):
                        break
                except OSError:
                    if time.monotonic() >= deadline:
                        raise TimeoutError("server did not listen within 30 seconds")
                    time.sleep(0.2)
            actual = snapshots(base)
            if stopped or os.getppid() != args.parent_pid:
                raise KeyboardInterrupt
            if args.compare:
                assert actual == json.loads(args.compare.read_text()), "API snapshots changed during migration"
            if args.capture:
                args.capture.write_text(json.dumps(actual, indent=2, sort_keys=True) + "\n")
            print("Verified live API create, step, run, GET, and 404 behavior for just_tx default, firewall helper completion, upload validation, and replay.")
            if args.compare:
                print("All snapshots match the pre-migration baseline.")
        except BaseException:
            log.seek(0)
            print(log.read())
            raise
        finally:
            stop_processes([server])


if __name__ == "__main__":
    main()
