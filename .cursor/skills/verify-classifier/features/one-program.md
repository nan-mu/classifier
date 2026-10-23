# One program

One program runs a single `[[program]]` row from `profile.toml`. The create, run, and compare steps are the same as the full suite, limited to that name.

## Sub-features

- `program-incr` runs `incr`, whose images are `../build/incr/incr.elf` and `../build/incr/bpf.o`.
- `program-named` runs any other `name` in the profile, including `just_tx`, `firewall`, `merge_try`, and `helper_loop`.
- `program-missing` rejects a name that is not in the profile.

## How to get to it (user POV)

- Run `classifier test --program <name>` from the classifier root.
- The same command with `CLASSIFIER_PROFILE` set to a profile file that contains `<name>`.

## Driving it with the classifier CLI

Preconditions:

- `python3 .cursor/skills/verify-classifier/scripts/doctor.py` exits 0.
- The doctor output contains `program incr expect weak` when the row under test is `incr`.
- `../build/incr/incr.elf` and `../build/incr/bpf.o` are files when the row is `incr`.
- `CLASSIFIER_DUMP_FAILS` is unset.

- **Run incr.** Ask for that row only. Run `python3 .cursor/skills/verify-classifier/scripts/drive.py --program incr`. The printed path is the evidence directory.
- **Pass.** `exit_code.txt` is `0`. `stdout.txt` has `payload.passed` `1`, `payload.failed` `0`, and one case `profile.incr` with `detail` `pass`. `stderr.txt` contains `profile incr expect weak` and `profile incr ok pass`.
- **Run another name.** Replace `incr` in the command with a `name` doctor printed, for example `square`. The case id in `stdout.txt` is `profile.<name>`, and stderr names that program.
- **Unknown name.** Run `python3 .cursor/skills/verify-classifier/scripts/drive.py --program not-a-program`. Exit code is `2`. `stdout.txt` has `ok` false and `error.code` `usage`. The message says `profile.toml has no program not-a-program`.

## Gotchas

- A green `incr` run does not verify `just_tx` or the rest of the profile. Those rows have their own images and their own `expect`.
- `--program` and `--root` are different flags. Passing `--root` selects the `case.json` walker and ignores the profile name.
- If doctor says the binary is older than the Lean libraries, rebuild with Launch before trusting a pass or a fail.
- `weak` fails closed when both sides complete and every branch expression unifies. That outcome would satisfy `strict`, not the current `incr` row.
