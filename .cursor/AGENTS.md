# Cursor harness guide

Canonical path: `.cursor/AGENTS.md`. There is no repo-root `AGENTS.md`.

## One harness

Cursor owns the full repository: `tooling/`, `doc/`, Lean4 / Lake sources,
`.cursor/`, `README.md`, and `.github/`. Edit Lean and `doc/` directly in this
session. Do not delegate to `omp`, `spec-author`, or any external agent harness.

## Specs, Lean, and end-to-end work

Current `doc/` specs define Create / Step / History / Merge / Merge-Step
semantics. They outrank older code, obsolete limits, and historical design
assumptions. Adapt the system to the current specs; do not weaken specs to
match old code. If a spec is internally ambiguous, resolve from the math and
the live expand flow — do not silently drop requirements.

**Lean ↔ `doc/` stay aligned.** Changing Lean behavior updates affected docs;
changing operation semantics updates Lean. Docs state math (I/O, preconditions,
state change, rules), not incidental implementation detail. Do not leave dead
docs as if they were still normative.

**Acceptance is a real runnable flow**, not compile / unit-test green alone.
When the task touches expand, merge, or the viewer:

1. Prefer fixing Lean semantics first, then tooling adapters and Web UI.
2. Merge and Merge-Step must actually run under current specs (not merely
   exist as APIs). Merge is not full-machine equality and is not state
   synthesis unless the spec allows it. History predicates must not vanish
   solely because a suffix is reused.
3. Verify with `lake run dev` (or live `/run`) and, when UI is in scope, a
   real Web UI create → step/run → complete path. Prefer fixtures that
   exercise merge (`merge_try`, etc.); “merge never fired” is not a pass.
4. Distinguish measured behavior from code-reading inference. Say what was
   not verified if the environment lacks a dependency.

## What Cursor owns

Rust/Cargo workspace under `tooling/`: Lean FFI binding, Expand HTTP API,
web graph viewer, fixtures, scripts, and CI — plus Lean math/implementation
under `Core/`, `Node/`, `RV32/`, `EBPF/`, and specs under
`doc/`.

```text
tooling/Cargo.toml              Rust workspace (one Cargo.lock)
tooling/lean-binding/           FFI to Lean create/step/merge (+ legacy test helpers)
tooling/lean-binding/tests/     binding and snapshot regressions
tooling/server/                 Kernel lib, axum `server` bin, JSON `classifier` bin
tooling/test/                   CaseSpec suites `base/`, `xdp/`, `fail/`
tooling/web/                    Vite + Kuma + xyflow viewer
tooling/scripts/dev.py          lake run dev supervisor
tooling/scripts/smoke.py        live API smoke
tooling/scripts/rust-ci.sh      nightly fmt + clippy gate
tooling/fixtures/just_tx.elf    default Compact XDP ELF
tooling/fixtures/xdp.elf        firewall / helper-call fixture
.github/workflows/rust.yml      mirrors rust-ci.sh
doc/                            math defs, proofs, research notes
Core/ Node/ RV32/ EBPF/         Lean libraries
Core/Cross/                     cross-arch normalize / unify
CrossArch/                      dual-arch fixtures (not in server dylibs)
```

Use Lake as the repo entrypoint (`lake build`, `lake test`, `lake run dev`).
Cargo and npm are component tools. Do not hard-code
`tooling/target/debug/server`; take the path from Cargo artifacts.
Keep one workspace lockfile. Validate Compact XDP ELF uploads via sibling
`tooling/vendor/xpost-elf`. Reject raw BIN uploads.

Default fixture budget notes used by tests/UI: HTTP/WebUI default budget
1024; budget 512 remains a fuel-exhaustion regression on `just_tx`.
Synthetic wrapper return address is `0x2000` (not an ELF field).

`classifier` (`tooling/server/src/bin/classifier.rs`) prints one Envelope JSON
per command. Exit 0 means `ok` true, exit 1 is a domain error, and exit 2 is
usage. `Kernel::execute` is the sync reducer for create, step, run, get, and
the compare commands (CLI/harness). HTTP handlers still gate Lean work with
`InferencePool`. `classifier test --root tooling/test` walks
`tooling/test/{base,xdp,fail}/**/case.json` in process. eBPF create binds map
LDDW slots from the `.bpf.o` REL section to companion Compact ELF map VMAs
(not hard-coded just_tx slot 34). `just_tx`, `just_drop`, `merge_try`, and `firewall` require both arches
`complete` and compare-tree `fail` 0. Suite `firewall` is a simplified
blacklist (no `ihl*4`, no UDP ctrl path) rebuilt with firmware `.xpost.mem`.
`base/helper_loop` uses `helper_loop.{elf,bpf.o}` and expects `LimitExceeded`
under budget 64 with helper predicates on the frontier (lookup in the loop).

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
  Export: `lean_expand_merge` in `Node/Merge.lean`.

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

If create/step behavior looks wrong, fix tooling adapters/tests first. When the
bug is in Lean semantics or `doc/`, edit those paths in this session and keep
docs aligned with code.

## Build and check

From repo root:

```bash
lake build
lake test
lake run dev          # API :8788 (PORT overrides), Vite :5173
```

After Lean or `doc/` edits that affect expand/merge semantics:

```bash
lake build Core Node RV32 EBPF
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
built Lean libs, and vendored `tooling/vendor/xpost-elf`.

Before reporting done: `git status` / `git diff`, preserve unrelated dirty
files, run checks that match what you edited. Do not commit unless asked.
Never commit `.codex/` or leftover `.omp/` directories.
