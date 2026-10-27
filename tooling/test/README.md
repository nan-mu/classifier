# Classifier tooling tests

Suites under `tooling/test/`.

## Suites

| Suite | Intent |
| --- | --- |
| `base/` | Create/step/run, branch and merge/loop control flow |
| `xdp/` | Product XDP pairs (RV32 Compact ELF + eBPF `.bpf.o`) |
| `fail/` | Expected reject, fuel fail, or compare-tree `fail` |

## Invoke

```bash
cargo run --manifest-path tooling/Cargo.toml -p server --bin classifier -- \
  test --root tooling/test
```

Each case is a `case.json` (CaseSpec). The in-process harness drives
`Kernel::execute` and checks `expect` / `assert`.

## XDP assets

Checked in under `xdp/{just_tx,just_drop,merge_try,firewall}/`.
eBPF Meta binds map LDDW slots from the `.bpf.o` REL section to companion
Compact ELF map VMAs (not hard-coded just_tx slot 34). The helper-completion
fixture `tooling/fixtures/xdp.elf` remains for expand unit tests only.

## Coverage notes

The command prints one Envelope. Exit 0 means every case matched `expect`. Exit 1 means a case failed. Exit 2 means usage, including a missing `--root`.

Measured on the current images:

- `just_tx`, `just_drop`, `merge_try`, and `firewall` dual runs finish
  `complete` on both arches with compare-tree `fail` 0. Firewall is a
  simplified blacklist (no `ihl*4`, no UDP ctrl path) so packet-key MapWrite
  and branch shapes unify.
- `base/helper_loop` uses `helper_loop.{elf,bpf.o}`. Both arches hit
  `LimitExceeded` under budget 64 with helper predicates on the frontier
  (map lookup inside the loop body).
