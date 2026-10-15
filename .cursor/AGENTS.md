# Cursor harness guide (tooling)

Canonical path: `.cursor/AGENTS.md`. There is no repo-root `AGENTS.md`.
Do not treat `.omp/AGENTS.md` as Cursor policy.

## Two harnesses (do not mix)

| Harness | Guide | Owns writes | Must refuse writes |
| --- | --- | --- | --- |
| **Cursor** (this chat) | `.cursor/AGENTS.md` | `tooling/`, `.cursor/`, `README.md`, `.github/` | `doc/`, Lean4 / Lake sources |
| **omp** | `.omp/AGENTS.md` | `doc/`, Lean4 / Lake sources — through a `spec-author` spawn | `tooling/` |

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
- `*.lean`, `ClassifierExpr/`, `PathMerge/`, `RV32IMC/`, `EBPF/`,
  `lakefile.lean`, `lean-toolchain`, `lake-manifest.json` when present

Allowed on those paths: read, search, cite. `lake build` / `lake test` only
as verification that does not rewrite them.

**Writable.** `.cursor/`, `README.md`, `tooling/`, `.github/`.

## Delegating to omp (Lean / `doc/` work)

Cursor never edits the frozen side. It delegates through the `omp` CLI and keeps
the integration and the final verification. Delegation is two hops, and the
second one is omp's own:

1. **Cursor → omp main session.** A one-shot brief, run non-interactively via
   **interactive fish** so the local `omp` wrapper injects `QWEN_API_KEY`
   (non-interactive `fish -c` exits `config.fish` before the function loads):
   `fish -ic 'omp -p @.cursor/omp-handoff-<task>.md'`.
   Keep the repo default model (`qianwen/...` in `.omp/config.yml`). Do not
   retarget the dispatcher to a bare `deepseek/...` id.
2. **omp main session → `spec-author`.** `.omp/config.yml` runs that session on a
   DeepSeek-via-QWEN model, and no CLI flag makes a session *be* a named agent
   (`omp --help` has `--model`, not `--agent`). `.omp/AGENTS.md` therefore
   requires it to spawn `spec-author` — pinned to `openai-codex/gpt-6.1-sol:high`
   — for every `doc/` or Lean edit, and forbids it from editing those paths itself.

**Briefs address the dispatcher, never assert an identity.** Asking for the spawn
is the contract:

```text
# Task: <what Cursor needs>
Spawn `agent: spec-author` for every doc/Lean item below; do not edit them yourself.
<tooling-side facts: measured node/fuel numbers, fixture paths, what Cursor changed>
```

- Never write "You are **omp** (`spec-author`)" and never attach
  `@.omp/agents/spec-author.md`. A main session that reads an identity adopts it
  and does the work on the DeepSeek model, so Codex never runs at all.
- Do not pin the main session to `openai-codex/...` to force Codex at the top
  level; the Codex work belongs to the spawned agent.
- Tooling-side facts go in the brief. omp reads `tooling/` freely and never edits
  it.

**Verification stays with Cursor.** After omp yields, read `git diff`, require
`lake build ClassifierExpr PathMerge RV32IMC EBPF` and the three `.audit/` doc
gates, then do the live `/run` check yourself. omp's prose is not evidence, and a
green build is not a semantic proof.

Handoff notes live in `.cursor/omp-handoff-<task>.md`, describe the tooling side
only, and are one-shot inputs — not agent definitions.

## What Cursor owns

Rust/Cargo workspace under `tooling/`: Lean FFI binding, Expand HTTP API,
web graph viewer, fixtures, scripts, and CI.

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
```

Use Lake as the repo entrypoint (`lake build`, `lake test`, `lake run dev`).
Cargo and npm are component tools. Do not hard-code
`tooling/target/debug/server`; take the path from Cargo artifacts.
Keep one workspace lockfile. Validate Compact XDP ELF uploads via sibling
`../xpost/xpost-elf` (need that checkout). Reject raw BIN uploads.

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
  Export: `lean_expand_merge` in `PathMerge/Merge.lean`.

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
handoffs for Lean or `doc/`: hand those to the `omp` CLI, which spawns its pinned
Codex `spec-author` (see "Delegating to omp").
