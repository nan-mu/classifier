---
name: verify-classifier
description: Drive classifier's profile.toml dual-arch CLI (`classifier test`) and capture the Envelope. Use when a Lean, create, step, or compare change must be shown against the programs listed in profile.toml.
---

# Verify classifier

The primary surface is the `classifier` CLI in `tooling/server`. `classifier test` with no `--root` reads `profile.toml` at the classifier root (or `CLASSIFIER_PROFILE`) and, for every `[[program]]`, creates an RV32 session from `elf`, an eBPF session from `bpf`, runs both to the 1024 budget, and compares the trees. The web UI (`lake run dev`, API `:8788`, Vite `:5173`) and `classifier test --root tooling/test` are separate surfaces. Do not treat either as a substitute for a profile row.

Images are read-only. Each invocation is its own process and its own in-memory `Kernel`. Two drives can run at once. They share nothing except CPU and, if set, the single file `CLASSIFIER_DUMP_FAILS` writes at `/tmp/compare-fails.json`. Leave that variable unset. Do not point `CLASSIFIER_PROFILE` at a copy in another directory unless you rewrite `build`. Paths are resolved from the profile file's parent, and the repo file uses `build = "../build"`.

## Launch

From the classifier root, build the Lean libraries and the CLI once.

```bash
lake build Core Node RV32 EBPF
lake env cargo build --manifest-path tooling/Cargo.toml -p server --bin classifier
```

Ready means `python3 .cursor/skills/verify-classifier/scripts/doctor.py` exits 0 and prints `profile`, `build`, `binary`, and one `program` line per `[[program]]`. A process that only answers `classifier` with no arguments is not enough. The images named by the profile must exist.

There is no server to leave running. Each drive below starts its own process.

## Doctor

```bash
python3 .cursor/skills/verify-classifier/scripts/doctor.py
```

The script is read-only. It fails when `profile.toml` or `CLASSIFIER_PROFILE` is missing or unparsable, when an `elf` or `bpf` path is not a file, when cargo metadata's debug `classifier` binary is missing, when that binary is older than `libclassifier_Core.dylib`, `libclassifier_Node.dylib`, `libclassifier_RV32.dylib`, or `libclassifier_EBPF.dylib`, or when the binary's no-argument probe does not exit 2 with usage text that mentions `classifier test`. Cargo metadata supplies the binary path. Do not hard-code `tooling/target`.

## Drive

Run doctor first. Then one of these, from the classifier root.

```bash
python3 .cursor/skills/verify-classifier/scripts/drive.py --program incr
python3 .cursor/skills/verify-classifier/scripts/drive.py --all
```

`--program` passes `classifier test --program <name>`. `--all` passes `classifier test` and walks every row. The wrapper records the command, cwd, profile path, pid, stdout, stderr, and exit code. Stdout is one Envelope JSON object. Exit 0 means `ok` is true. Exit 1 means one or more cases failed (`error.code` is `cases`). Exit 2 means usage, including an unknown program name.

Stderr is the progress log. A finished program prints `profile <name> expect <strict|weak|fail>` and then `profile <name> ok pass` or `profile <name> FAIL <detail>`.

What `expect` checks, from `tooling/server/src/profile.rs` and `harness.rs`:

- `strict`. Both sides `status` `complete`, compare-tree `fail` 0, `expr_incomplete` 0.
- `weak`. Both sides `complete`, `fail` 0, and `expr_incomplete` at least 1.
- `fail`. A side does not finish `complete`, or some compare node has `matchStatus` `fail`.

The current `profile.toml` sets every program to `weak`. Do not edit `expect` so a run turns green.

`classifier create --arch rv32imc --budget 1024 --program <name>` and `classifier create --arch ebpf --budget 1024 --program <name>` load the same files. They are not the profile test. A create Envelope does not prove the compare.

## Evidence

The wrapper prints one directory under `.audit/verify-classifier/<UTC>-<program-or-all>/`. That directory is gitignored. Keep it.

- `command.txt` is the argv.
- `stdout.txt` is the Envelope. `payload.passed`, `payload.failed`, and each `payload.cases[]` (`id`, `suite`, `ok`, `detail`) are the result.
- `stderr.txt` is the per-program progress.
- `exit_code.txt` is the process exit code.
- `summary.json` repeats `ok`, `payload`, and `error`.
- `pid` is the process that produced those files.

Proof is the command plus those files, not a claim that the binary compiled. A pass is exit 0 and `payload.ok` true for the programs you asked to run. A fail is exit 1 with the `detail` string. Do not drop a program from the profile to avoid a failure. `CLASSIFIER_DUMP_FAILS` is off unless you are inspecting a failure. If it is set, the extra artifact is `/tmp/compare-fails.json`, which a second drive will overwrite.

## Cleanup

```bash
python3 .cursor/skills/verify-classifier/scripts/cleanup.py .audit/verify-classifier/<stamp>-<label>
```

The argument must be a directory under `.audit/verify-classifier/`. Cleanup sends `SIGTERM` to the pid recorded there when that process is still running. It does not delete the directory. A drive that already exited has nothing to kill. Do not kill a `classifier` process by name.

## Helpers

- `python3 .cursor/skills/verify-classifier/scripts/doctor.py`
- `python3 .cursor/skills/verify-classifier/scripts/drive.py --program <name>`
- `python3 .cursor/skills/verify-classifier/scripts/drive.py --all`
- `python3 .cursor/skills/verify-classifier/scripts/cleanup.py <evidence-dir>`

The feature map is `features/README.md`.
