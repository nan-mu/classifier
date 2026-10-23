# Create from profile

Create from profile loads one architecture image named by `profile.toml` and returns a session Envelope. It does not run the other architecture and it does not compare trees.

## Sub-features

- `create-rv32` loads the row's `elf` as `rv32imc`.
- `create-ebpf` loads the row's `bpf` as `ebpf` and uses that row's `elf` as the map image.
- `create-default` with no `--program` and no `--image` loads `just_tx`.

## How to get to it (user POV)

- Run `classifier create --arch rv32imc --budget 1024 --program <name>`.
- Run `classifier create --arch ebpf --budget 1024 --program <name>`.
- Run `classifier create --arch rv32imc --budget 1024` to load `just_tx`.

## Driving it with the classifier CLI

Preconditions:

- `python3 .cursor/skills/verify-classifier/scripts/doctor.py` exits 0.
- Doctor lists `program incr` and both of its image paths.
- Launch has been run, so the binary is not older than the Lean libraries.

- **Create the RV32 session.** From the classifier root, run `lake env cargo run --quiet --manifest-path tooling/Cargo.toml -p server --bin classifier -- create --arch rv32imc --budget 1024 --program incr`. Exit code is `0`. Stdout is one Envelope with `"command":"create"` and `"ok":true`. `session_id` is a non-empty string. The payload is the root snapshot for that image.
- **Create the eBPF session.** Run `lake env cargo run --quiet --manifest-path tooling/Cargo.toml -p server --bin classifier -- create --arch ebpf --budget 1024 --program incr`. Exit code is `0`. Stdout is a second Envelope with a different `session_id` and `"ok":true`.
- **Confirm the process exited.** The shell prompt returns. Nothing is listening on `8788` because of this command. A later `classifier get` in a new process cannot see the session. The session lived only in the process that just exited.

## Gotchas

- A successful create does not prove `classifier test --program incr`. The profile test also runs both sides and compares them.
- `--image` bypasses the profile path. A proof of this feature omits `--image`.
- `--arch ebpf` without a profile row fails usage when the `bpf` file is missing. Doctor is the check for that precondition.
- These commands are not wrapped by `drive.py`. Save stdout, stderr, and the exit code yourself under `.audit/verify-classifier/` if you need a proof artifact. Cleanup must not delete that directory.
