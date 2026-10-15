# Synthesis draft (pre-arena; finalize after candidates)

## Named data shape

`CaseSpec` + `Command` enum + JSON `Envelope { ok, data?, error? }`.
Harness interprets CaseSpec. Domain exposes `execute(Command) -> Envelope`.
Server maps HTTP to Command. CLI prints Envelope JSON on stdout.

## Preferred crate shape (pending arena)

```text
tooling/server/src/lib.rs     # domain: expand, engine, pred_*, images, driver, api::execute
tooling/server/src/main.rs    # axum only
tooling/server/src/bin/classifier.rs  # JSON CLI
tooling/test/{base,xdp,fail}/ # CaseSpec + assets
tooling/test/run.py           # walks manifests, invokes classifier, asserts expect
```

## Rubric for arena pick

1. Public surface size (fewer crates/exports wins if still meets brief).
2. CaseSpec is data-driven (no suite if/else sprawl).
3. Server and CLI share one execute path (no duplicated session create).
4. Migration risk (moves vs rewrites of expand/engine).
5. Fail cases can assert without HTTP.

## XDP pack (assets already copied)

`tooling/test/xdp/{just_tx,just_drop,merge_try,firewall}/{name}.elf` + `{name}.bpf.o`
from `/Volumes/SSD/bs/build/<prog>/`.

## Base pack (planned)

- `create_default`: default just_tx create → status running/complete path.
- `branch_firewall`: firewall.elf run emits taken/not-taken preds.
- `helper_loop`: synthetic RV32 words from helper_calls loop (or fib.elf if create works).

## Fail pack (planned)

- `raw_bin_reject`: esp32c3.bin → error.
- `truncated_elf`: just_tx.elf[:-1] → error.
- `budget_512_exhaust`: just_tx budget 512 → status fail (fuel).
- `compare_tree_mismatch`: hand-built SnapRun pair → fail >= 1.