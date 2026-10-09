import argparse
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
    with urllib.request.urlopen(req, timeout=10) as response:
        return json.load(response)


def snapshots(base):
    result = {}
    for program, budget in [("demo", 11), ("demo", 10), ("esp32c3", 3)]:
        created = request(base, "POST", "/api/session", {"program": program, "budget": budget})
        path = "/api/session/" + created["id"]
        stepped = request(base, "POST", path + "/step", {})
        done = request(base, "POST", path + "/run", {})
        assert request(base, "GET", path) == done, "GET must return the final snapshot"
        expected = "complete" if program == "demo" and budget == 11 else "fail"
        assert done["status"] == expected, (program, budget, done["status"])
        if expected == "fail":
            assert done["reason"] == "LimitExceeded", done["reason"]
        assert len(stepped["nodes"]) > len(created["nodes"]), "step must expand the graph"
        result[f"{program}/{budget}"] = [created, stepped, done]
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
            print("Verified live API create, step, run, GET, and 404 behavior for demo and esp32c3.")
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
