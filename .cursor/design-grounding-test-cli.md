# Grounding: classifier domain / CLI / test harness

## Overview

Today `tooling/server` is a fat binary. `main.rs` owns HTTP + session map +
default fixtures. Domain logic lives beside it as modules (`expand`, `engine`,
`pred_tree`, `pred_match`, `rv32_image`, `bpf_image`, `driver/*`). Frontend talks
HTTP. There is no first-class library crate and no JSON CLI for offline tests.

## Key Concepts

- **Session / Snapshot.** Lean-backed expand graph. Create → step / run → snapshot JSON.
- **Compare tree.** Host `build_compare_tree` over two SnapRuns → `matchStatus` pass/fail.
- **Compact XDP ELF.** RV32 path via `xpost-elf`. eBPF path via `.bpf.o` insn extract + product meta.
- **Fixtures in use.** `just_tx.{elf,bpf.o}`, `just_drop.elf`, `merge_try.elf`, `xdp.elf` (firewall).

## How It Works

1. HTTP `POST /api/session` parses arch + bytes → `Session::new` / `new_ebpf`.
2. `run` drives Lean through `InferencePool` until complete/fail.
3. Dual compare posts two snapshots to `/api/compare/tree`.

## Where Things Live

| Concern | Path |
| --- | --- |
| HTTP surface | `tooling/server/src/main.rs` |
| Expand session | `tooling/server/src/expand.rs` |
| Compare tree | `tooling/server/src/pred_tree.rs` |
| Embedded fixtures | `tooling/fixtures/` + `include_bytes!` in image modules |
| Build artifacts (source of truth) | `/Volumes/SSD/bs/build/<prog>/{<prog>.elf,bpf.o}` |
| Loop regression (synthetic words) | `tooling/lean-binding/tests/helper_calls.rs` |

## Constraints for the redesign

- Cursor may write only `tooling/`, `.cursor/`, `README.md`, `.github/`.
  Put the suite under `tooling/test/`, not repo-root `test/`.
- Do not reimplement Lean semantics in Rust.
- CLI must emit JSON so harness asserts on structure, not text scrape.
- Suites: `base` (API + branch/loop predicates), `xdp` (four product programs dual-arch),
  `fail` (expected reject / fail / matchStatus fail).
- Extract domain so server and CLI share one crate. Frontend keeps HTTP.

## Named data shape (CaseSpec)

```text
CaseSpec {
  id: String,
  suite: base | xdp | fail,
  expect: {
    kind: pass | fail | error,   // harness outcome
    status?: complete | fail,    // session.status when relevant
    http?: 4xx,                  // or CLI exit + error object
    compare_tree?: { fail: 0 } | { fail: >=1 },
  },
  artifacts?: { rv32: path, ebpf: path },  // relative to case dir
  budget?: u32,
  steps: [ create | run | compare_tree | ... ],
  assert: JSONPath-ish checks on last JSON envelope
}
```

Organizing structure: **typed CaseSpec registry + command enum**, not scattered
if/else per suite. Harness is a pure interpreter over CaseSpec.