# Profile suite

The profile suite runs every program in `profile.toml`. For each row it creates RV32 from `elf`, creates eBPF from `bpf`, runs both, and compares the trees against that row's `expect`.

## Sub-features

- `suite-all` walks every `[[program]]` in order and emits one Envelope.
- `suite-weak` checks a row whose `expect` is `weak`. Both sides complete, kind counts match, and at least one branch expression does not unify.
- `suite-strict` checks a row whose `expect` is `strict`. Both sides complete, kind counts match, and every compared branch expression unifies.
- `suite-fail` checks a row whose `expect` is `fail`. A side does not complete, or some segment's kind counts disagree.

## How to get to it (user POV)

- Run `classifier test` from the classifier root with no `--root` and no `--program`.
- The same command with `CLASSIFIER_PROFILE` set to a profile file.

## Driving it with the classifier CLI

Preconditions:

- `python3 .cursor/skills/verify-classifier/scripts/doctor.py` exits 0 and lists every program you expect to run.
- Every listed `elf` and `bpf` is a file.
- `CLASSIFIER_DUMP_FAILS` is unset.

- **Run the suite.** Ask for every profile row. Run `python3 .cursor/skills/verify-classifier/scripts/drive.py --all`. The printed path is the evidence directory. `exit_code.txt` is `0` and `summary.json` has `"ok": true` when every row matches its `expect`.
- **Read the per-program log.** Open `stderr.txt` in that directory. Each program has a `profile <name> expect <expect>` line and a later `profile <name> ok pass` line.
- **Read the Envelope.** Open `stdout.txt`. `command` is `test`. `payload.passed` equals the number of `[[program]]` rows. `payload.failed` is `0`. Each `payload.cases[]` has `suite` `profile`, `id` `profile.<name>`, `ok` true, and `detail` `pass`.
- **A mismatch.** When a row does not match, the process exits 1. `summary.json` has `"ok": false` and `error.code` `cases`. The failing `payload.cases[]` `detail` is the reason. `stderr.txt` contains `profile <name> FAIL` plus that detail.

## Gotchas

- `classifier test --root tooling/test` does not read `profile.toml`. It runs the `case.json` suites.
- Copying `profile.toml` to another directory without rewriting `build` makes `../build` point at the wrong tree. Doctor then reports missing images.
- The current profile sets every program to `weak`. A run that completes with zero incomplete branch expressions fails a `weak` row, because `weak` requires `expr_incomplete` at least 1.
- Do not change `expect` to make the suite pass. Record the `detail` string.
- The suite budget is 1024 for every row. A smaller budget is a different test.
