import argparse
import os
from pathlib import Path
import signal
import socket
import subprocess
import sys
import time


def stop_processes(processes):
    for process in processes:
        try:
            os.killpg(process.pid, signal.SIGTERM)
        except (ProcessLookupError, PermissionError):
            pass
    deadline = time.monotonic() + 5
    while time.monotonic() < deadline:
        alive = False
        for process in processes:
            process.poll()
            try:
                os.killpg(process.pid, 0)
                alive = True
            except ProcessLookupError:
                pass
            except PermissionError:
                # macOS reports EPERM for a group containing only unreaped zombies.
                alive = True
        if not alive:
            break
        time.sleep(0.05)
    for process in processes:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass
        process.wait()


def check_ports(ports):
    for port in ports:
        with socket.socket() as sock:
            sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            try:
                sock.bind(("127.0.0.1", port))
            except OSError as error:
                raise RuntimeError(f"Port {port} is unavailable: {error}") from error


def main():
    parser = argparse.ArgumentParser(description="Supervise the development API and frontend.")
    parser.add_argument("--server", type=Path, required=True)
    parser.add_argument("--parent-pid", type=int, default=os.getppid())
    args = parser.parse_args()
    tooling = Path(__file__).resolve().parents[1]
    processes = []
    stopped = None

    def stop(signum, _frame):
        nonlocal stopped
        stopped = signum

    signal.signal(signal.SIGHUP, stop)
    signal.signal(signal.SIGINT, stop)
    signal.signal(signal.SIGTERM, stop)
    try:
        ports = [int(os.environ.get("PORT", "8788")), 5173]
        check_ports(ports)
        commands = [
            ([str(args.server.resolve())], tooling),
            (["npm", "run", "dev", "--", "--host", "127.0.0.1", "--port", "5173", "--strictPort"], tooling / "web"),
        ]
        for command, cwd in commands:
            if os.getppid() != args.parent_pid:
                stopped = signal.SIGTERM
            if stopped is not None:
                return 128 + stopped
            processes.append(subprocess.Popen(command, cwd=cwd, start_new_session=True))
        pending = set(ports)
        deadline = time.monotonic() + 30
        while stopped is None:
            if os.getppid() != args.parent_pid:
                return 128 + signal.SIGTERM
            for process in processes:
                result = process.poll()
                if result is not None:
                    raise RuntimeError(f"Development process {process.args[0]} exited with code {result}")
            for port in list(pending):
                try:
                    with socket.create_connection(("127.0.0.1", port), timeout=0.2):
                        pending.remove(port)
                except OSError:
                    pass
            if pending and time.monotonic() >= deadline:
                raise TimeoutError(f"Development services did not listen on ports {sorted(pending)}")
            time.sleep(0.1)
        return 128 + stopped
    except (OSError, RuntimeError, ValueError) as error:
        print(error, file=sys.stderr)
        return 1
    finally:
        stop_processes(processes)


if __name__ == "__main__":
    sys.exit(main())
