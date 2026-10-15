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
(`tooling/fixtures/xdp.elf`); the newer `build/firewall/firewall.elf` is kept
as `firewall.bpf.o` companion only until RV32 expand completes on that image.

## Coverage notes

The command prints one Envelope. Exit 0 means every case matched `expect`. Exit 1 means a case failed. Exit 2 means usage, including a missing `--root`.

Measured on the current images:

- `just_tx` dual run finishes `complete` on both arches, and compare-tree `fail` is 0.
- `merge_try` does the same. Compare-tree `fail` is also 0.
- `firewall` and `just_drop` cases assert RV32 `complete` only. Their eBPF runs
  still stop early (`LocalReject` / `UndefinedSrc` under just_tx product meta);
  dual complete is not a hard gate until that is fixed.
