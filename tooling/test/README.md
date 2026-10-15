# Classifier tooling tests

Cursor-owned suite under `tooling/test/` (harness write scope is `tooling/`).

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

Copied from `/Volumes/SSD/bs/build/<prog>/` into `xdp/{just_tx,just_drop,merge_try,firewall}/`.
`firewall.elf` in this suite is the known helper-completion fixture
(`tooling/fixtures/xdp.elf`); the newer `build/firewall/firewall.elf` does not
yet complete under RV32 expand, so firewall stays RV32-only until a matching
pair is ready. eBPF Meta binds map LDDW slots from the `.bpf.o` REL section to
companion Compact ELF map VMAs (not hard-coded just_tx slot 34).

## Coverage notes

The command prints one Envelope. Exit 0 means every case matched `expect`. Exit 1 means a case failed. Exit 2 means usage, including a missing `--root`.

Measured on the current images:

- `just_tx`, `just_drop`, and `merge_try` dual runs finish `complete` on both
  arches with compare-tree `fail` 0.
- `firewall` asserts RV32 `complete` only (asset mismatch for eBPF dual).
- `base/helper_loop` uses the `fib` Compact ELF / bpf pair. Both arches hit
  `LimitExceeded` under budget 64: fib's control-flow loop grows the frontier
  faster than that fuel allows.
