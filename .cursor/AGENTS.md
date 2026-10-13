# Cursor harness guide (tooling)

Canonical path: `.cursor/AGENTS.md`. There is no repo-root `AGENTS.md`.
Do not treat `.omp/AGENTS.md` as Cursor policy.

## Two harnesses (do not mix)

| Harness | Guide | Owns writes | Must refuse writes |
| --- | --- | --- | --- |
| **Cursor** (this chat) | `.cursor/AGENTS.md` | `tooling/`, `.cursor/`, `README.md`, `.github/` | `doc/`, Lean4 / Lake sources |
| **omp** | `.omp/AGENTS.md` | `doc/`, Lean4 / Lake sources | `tooling/` |

**注意事项.**

1. Never import the other harness's write scope.
2. Lean / `doc/` edits belong to omp or a human. Cursor refuses them.
3. `tooling/` edits belong to Cursor. omp refuses them.
4. Split cross-harness tasks. Do not touch the frozen side "to help".
5. Always-on freeze text lives in `.cursor/rules/cursor-harness.mdc`
   (`alwaysApply: true`). Keep it aligned with this file.

## Freeze: `doc/` and Lean4 are read-only

Refuse create/edit/delete/rename/move/regenerate/format of:

- `doc/**`
- `*.lean`, `CommonMath/`, `RV32IMC/`, `EBPF/`, `lakefile.lean`,
  `lean-toolchain`, `lake-manifest.json` when present

Allowed on those paths: read, search, cite. `lake build` / `lake test` only
as verification that does not rewrite them.

**Writable.** `.cursor/`, `README.md`, `tooling/`, `.github/`.

## What Cursor owns

Rust/Cargo workspace under `tooling/`: Lean FFI binding, Expand HTTP API,
web graph viewer, fixtures, scripts, and CI.

```text
tooling/Cargo.toml              Rust workspace (one Cargo.lock)
tooling/lean-binding/           FFI to Lean create/step/merge (+ legacy test helpers)
tooling/lean-binding/tests/     binding and snapshot regressions
tooling/server/                 axum Expand API, ExpandSession, InferencePool
tooling/web/                    Vite + Kuma + xyflow viewer
tooling/scripts/dev.py          lake run dev supervisor
tooling/scripts/smoke.py        live API smoke
tooling/scripts/rust-ci.sh      nightly fmt + clippy gate
tooling/fixtures/just_tx.elf    default Compact XDP ELF
tooling/fixtures/xdp.elf        firewall / helper-call fixture
.github/workflows/rust.yml      mirrors rust-ci.sh
```

Use Lake as the repo entrypoint (`lake build`, `lake test`, `lake run dev`).
Cargo and npm are component tools. Do not hard-code
`tooling/target/debug/server`; take the path from Cargo artifacts.
Keep one workspace lockfile. Validate Compact XDP ELF uploads via sibling
`../xpost/xpost-elf` (need that checkout). Reject raw BIN uploads.

Default fixture budget notes used by tests/UI: HTTP/WebUI default budget
1024; budget 512 remains a fuel-exhaustion regression on `just_tx`.
Synthetic wrapper return address is `0x2000` (not an ELF field).

## Lean surface for tooling: create, step, merge

Rust must not reimplement instruction semantics. Against Lean, tooling's
supported expand contract is three stateless String FFI calls (via
`lean-binding`):

- `expand_create(metaJson)` → root SemState snapshot JSON (no `fuel` field).
  **Arch-specific** today (`lean_rv32_expand_create`).
- `expand_step(insns, metaJson, event, j, exprsJson, predsJson)` →
  `{status, reason, successors}` (applied SemStates) or a rejection.
  Step remains RV32-exported (`lean_rv32_expand_step`) until a neutral step
  export exists; treat the JSON contract as arch-neutral at the boundary.
- `expand_merge(requestJson)` → exact-config merge verdict JSON
  (`merged` / `reject`). Request is arch-neutral: `taken` + `notTaken[]`
  applied snapshots and `observationModel: HelperOnly` (no program / Meta).
  Export: `lean_expand_merge` in `CommonMath/Merge.lean`.

No Lean expand object stays alive across calls. Legacy snapshot helpers may exist
for tests; do not grow new product paths on them.

**Rust owns** session graph, Agenda schedule, edges, `fuel`/budget, merge-step
loop, and concurrency (`tooling/server/src/engine.rs`, `tooling/server/src/driver/`):

- `ExpandSession` holds `insns`, applied graph snapshot, Agenda, `MergePort`, fuel.
- Agenda ready set encodes NotTaken-before-Taken for an open branch frame;
  after NotTaken completes, Taken unblocks.   Nested Taken/NotTaken opens a new
  frame for BlockedTaken scheduling, but outer frames still inherit the nested
  NotTaken root (and later Ok descendants) into `pending_not_taken` /
  `not_taken_candidates`; outer Taken waits on both nested roots (join tips often
  lie on nested NotTaken). Never park nested Taken under an outer NT pending set.
  **Merge-step:** after each Taken
  head commits successors, `MergePort` compares the Taken tip to NotTaken suffix
  candidates; `InsufficientEvidence` keeps expanding Taken; `merged` records
  `mergeReuseFrom` plus a `reuse` edge and stops redundant Taken suffix work;
  `Counterexample` closes the frame. Snapshot `work` lists ready ids only.
- `InferencePool` has 10 Tokio permits gating `spawn_blocking` Lean jobs.
- `lean-binding` runs a fixed pool of 10 OS threads (`LEAN_WORKERS`) after
  one process-wide Lean init. Permit count matches worker count.
- HTTP `/create`, `/step`, `/run`, `/run/ws`, `/get` take a pool permit.
- UI “运行到结束” uses `GET /api/session/{id}/run/ws` (one snapshot per
  Agenda-ready wave, then `done`). POST `/run` is for smoke/tests.
- Linear ready set (`work` length 1): one Lean worker per wave. Multiple
  ready heads: `step_wave` expands up to 10 in parallel, commits in order.
  UI `/step` expands a single ready head.

**Wire facts tooling must honor** (consume, do not redefine semantics):

- `Meta`: `base`, `helperAddress` (dispatcher), `returnAddress` default
  `0x2000`; ignore unknown fields.
- Expr rows: value bindings plus optional `role: "constraint"` for
  comparisons. Legacy Predicate `kind: "cmp"` is rejected.
- Predicate rows: opaque five-class `kind` + fields (`helper`, `branch`,
  `ret`, `mapWrite` / `map_write`, `packetWrite` / `packet_write`; UI also
  formats `mapLookup`). No closed field enum in Rust/TS.
- A rejected step must not mutate the graph. Unknown target / missing source
  must not become a silent Exit or empty success.

If create/step behavior looks wrong, fix tooling adapters/tests first. Changing
Lean belongs to omp.

## Build and check

From repo root:

```bash
lake build
lake test
lake run dev          # API :8788 (PORT overrides), Vite :5173
```

After any change under `tooling/**/*.rs`, `tooling/**/Cargo.toml`,
`tooling/Cargo.lock`, `tooling/clippy.toml`, `tooling/rustfmt.toml`, or
`tooling/scripts/rust-ci.sh`:

```bash
lake build            # if Lean libs are stale; not part of rust-ci.sh
./tooling/scripts/rust-ci.sh
```

`rust-ci.sh` runs nightly `cargo fmt --check` on workspace crates
(`lean-binding`, `server` only) then nightly `clippy -D warnings`
(deny `dbg_macro` / `todo` / `unimplemented`; see `tooling/clippy.toml`).
Artifacts go to `tooling/target-nightly/`. Needs nightly rustup components,
built Lean libs, and sibling `../xpost`.

Before reporting done: `git status` / `git diff`, preserve unrelated dirty
files, run checks that match what you edited. Do not commit unless asked.
Never commit `.codex/` or `.omp/`.

## Model policy

Follow `~/.cursor/rules/model-access.mdc`. Cursor parent and Task subagents use
**Auto** only. Do not pin paid Task model slugs. Do not open Codex/MCP write
handoffs for Lean or `doc/` (omp owns those).
