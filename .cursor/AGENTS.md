# Cursor harness guide

Canonical path: `.cursor/AGENTS.md`. There is no repo-root `AGENTS.md`.
Do not treat `.omp/AGENTS.md` as Cursor policy.

## Two harnesses

| Harness | Guide | Owns writes | Refuse writes |
| --- | --- | --- | --- |
| **Cursor** | `.cursor/AGENTS.md` | `tooling/`, `.cursor/`, `README.md`, `.github/` | `doc/`, Lean4 / Lake |
| **omp** | `.omp/AGENTS.md` | `doc/`, Lean4 / Lake | `tooling/` |

Do not mix write scopes. Lean or `doc/` edits belong to omp. Tooling edits belong here.
`.omp/` is gitignored. Always-on Cursor loading is `.cursor/rules/cursor-harness.mdc`.

## Freeze (Cursor)

Refuse create/edit/delete/rename/move/regenerate/format of `doc/**`, `*.lean`,
`CommonMath/`, `RV32IMC/`, `EBPF/`, `lakefile.lean`, `lean-toolchain`, and
`lake-manifest.json`. Read and cite only. `lake build` / `lake test` are fine
when they do not rewrite those paths.

## Focus: `create` and `step`

Cursor work centers on the two Lean expand FFI entry points and the Rust engine
that owns the graph around them. Do not grow a second instruction semantics layer
in Rust. Call Lean for head inference; keep session state in the server.

### `create`

- Binding: `lean_rv32_expand_create` → Rust `rv32::expand_create`.
- Input: `Meta` JSON only (`base`, `helperAddress`, `returnAddress` default
  `0x2000`; unknown fields ignored). No `fuel`, no instruction image.
- Output: root SemState snapshot (expressions + predicates). No expand object
  remains in the Lean heap.
- HTTP: creating a session calls this once, then the engine attaches `fuel` /
  budget and the decoded `insns` image on the Rust side.

### `step`

- Binding: `lean_rv32_expand_step` → Rust `rv32::expand_step`.
- Input: `insns` (u32 words), `Meta`, dynamic helper `event`, head index `j`,
  `exprsJson`, `predsJson` for the current SemState.
- Output: `{status, reason, successors}` with applied successor SemStates, or a
  rejection. No `fuel` field from Lean.
- Contract: Lean is stateless and fuel-free. A rejected step must not mutate the
  Rust graph. Prepare successors before appending nodes or edges.
- Expr rows may include `role: "constraint"` for comparisons. Predicates are
  `Ret ⊔ Helper` only. Legacy `kind: "cmp"` Predicate input is rejected.

### Rust ownership around the two calls

`tooling/server` `ExpandSession` owns `insns`, work queue, edges, and `fuel`.
HTTP `/create`, `/step`, `/run`, `/run/ws`, `/get` go through that engine.
`lean-binding` runs FFI on a fixed pool of 10 Lean worker threads; the server
`InferencePool` permit count matches. UI `/step` expands one head; a work-queue
wave may expand up to 10 heads in parallel, then merge in queue order.

Legacy snapshot exports (`expand_bound_words_snapshot`, builtin fixture replay)
are not the primary API. Prefer `create` + `step`.

## Checks after tooling edits

From the repository root, when you change `tooling/**/*.rs` or related Cargo /
clippy / rustfmt / `rust-ci.sh` files:

```bash
lake build
./tooling/scripts/rust-ci.sh
```

Do not commit unless asked. Never commit `.codex/` or `.omp/`.
