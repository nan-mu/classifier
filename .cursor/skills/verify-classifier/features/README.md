# Classifier profile verification map

This directory is the maintained source for verifying `classifier test` against `profile.toml`. Read the index before driving, then use the matching feature file as the recipe.

## Baseline preconditions

- Working directory is the classifier root, the directory that contains `profile.toml` and `lakefile.lean`.
- Launch has built `Core`, `Node`, `RV32`, `EBPF`, and the `classifier` binary.
- `python3 .cursor/skills/verify-classifier/scripts/doctor.py` exits 0.
- `CLASSIFIER_DUMP_FAILS` is unset.
- `CLASSIFIER_PROFILE` is unset, or it points at a profile file whose `build` still resolves to the image tree you mean to read.
- Do not start a second drive that sets `CLASSIFIER_DUMP_FAILS`. Two ordinary drives may run together. They do not share a port or a session store.

## Driving conventions

- Start every recipe from a successful doctor run.
- Treat every command as literal. Keep the program name and flags unchanged.
- Run the profile test only through `python3 .cursor/skills/verify-classifier/scripts/drive.py`.
- A `classifier create` Envelope is a different entry point. It does not verify a compare.
- Leave `.audit/verify-classifier/` in place after cleanup.

## Proof and skip reporting

- Capture the command, stdout Envelope, stderr progress, and exit code.
- Record the feature ID and the program name with every artifact. The evidence directory name already contains the program or `all`.
- Report an unreachable program with the attempted command and the unmet precondition, usually a missing `elf` or `bpf` from doctor.
- Do not report a single-program run as verification of the full profile, or a create call as verification of `classifier test`.

## Feature entry contract

Each feature file starts with an H1 title and one paragraph describing the user-visible behavior. It then uses exactly four H2 sections in this order.

1. `Sub-features` lists short IDs with one line for each behavior.
2. `How to get to it (user POV)` lists every user entry point.
3. `Driving it with the classifier CLI` starts with `Preconditions:` and uses labeled bullets that pair each user action with an exact command and observable result.
4. `Gotchas` lists traps that can waste or invalidate a verification run.

## Features

- [Profile suite](./profile-suite.md) runs every `[[program]]` in `profile.toml`.
- [One program](./one-program.md) runs one named row, including `incr`.
- [Create from profile](./create-from-profile.md) loads one architecture image named by the same file. It does not compare trees.
