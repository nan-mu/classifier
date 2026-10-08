# Classifier repository guide for AI agents

`CommonMath` is the root. It owns architecture-agnostic Reg / Term / Expr /
solve / history shells (`doc/common-math.md`).

`RV32IMC` is a thin ISA layer that only defines:
- `Insn` (decoded instruction)
- `encode` / `encodeCompressed` (bits → Insn)
- `expr` (ExprSet × Insn ⇀ ExprSet)

RV32 uses `CommonMath.Reg` / `Term` / `ExprSet`. Do not grow RV32 with shared
math, register ADTs, or Sail execute stubs.

## Layout

```text
CommonMath.lean                 root reexports
CommonMath/{Bits,Reg,Numeric,Op,Term,Expr,Direction,Insn,Path,Render,Expand,Demo,Ffi}.lean
RV32IMC.lean                    imports Insn + Encode + Expr + Initial + Expand
RV32IMC/Insn.lean               decoded Insn + field tags
RV32IMC/Encode.lean             encode / encodeCompressed
RV32IMC/Expr.lean               expr / step (+ FFI smoke exports)
RV32IMC/Initial.lean            EntryParams + E0 (real ∪ xdp_md SW slots)
RV32IMC/Expand.lean             rv32Step / rv32Snapshot (+ lean_rv32_expand_snapshot)
RV32IMC/Esp32c3Program.lean     generated `esp32c3Words` from `esp32c3.bin`
doc/rv32-initial-expr.zh.md     RV32 entry E0 spec
esp32c3.bin                     XDP image under test (partition/label via `riscv-isa` in debug_server)
lean_binding/                   Rust FFI binding to Lean @[export]s (incl. demoSnapshot)
debug_server/                   axum §18 Expand debug API (Lean-backed; insn stream via riscv-isa)
debug_web/                      Vite + Kuma UI + xyflow canvas for that API
xtask/                          `cargo xtask demo` one-shot launcher
doc/common-math.md
doc/rv32imc-expr-value-functions.md
```

## Build & check

```bash
lake build
lake build RV32IMC
cargo test -p lean_binding
cargo test -p debug_server
cargo xtask demo   # lake build + debug_server :8788 + Vite :5173 (Ctrl-C stops both)
```

Toolchain: `leanprover/lean4:v4.29.0`. After layout changes: **Lean 4: Restart Server**.

## Lean4 via MCP Codex subagent

Any Lean4 reasoning or programming (`*.lean`, `lakefile*`, `lake-manifest.json`,
`lake build`, theorem/proof work, or FFI that exists only to expose Lean exports)
is done by **Codex**, invoked through the Cursor MCP namespace
`user-codex-subagent` — not by the main agent editing Lean, and not by pasting
into a human-run Codex session.

### Hard constraints (main agent)

- Do **not** implement or edit Lean4 sources for the Lean portion of the task.
- Do **not** call Codex CLI directly (`codex exec`, wrappers, quota gates).
- Do **not** pin Cursor Task paid model slugs solely to do the Lean work.
- Non-Lean glue (Rust/TS/docs that are not Lean) may proceed only when it does
  not require guessing unfinished Lean APIs; otherwise wait for Codex completion.

### Invoke Codex

1. Write a self-contained brief (see below) to a **gitignored** file under
   `.codex/` (directory is in `.gitignore`). Prefer `.codex/lean-handoff.md`
   (overwrite per task). Never commit `.codex/`.
2. Call MCP `user-codex-subagent` → `spawn_agent` with that brief as `prompt`
   (absolute repo root / cwd context must be in the prompt text). For independent
   Lean sub-tasks, use `spawn_agents_parallel` with one `{ "prompt": "..." }`
   per agent.
3. When the MCP call returns, verify yourself: `git status` / `git diff`, then
   run the brief’s done checks (`lake build`, `lake build RV32IMC`, targeted
   tests). Continue the parent task from that evidence, or spawn again if Lean
   work is still incomplete.

Prompt content requirements (same substance as user rule `lean4-codex-handoff`):
absolute repo root and working directory; plain-language goal; constraints from
this file (e.g. CommonMath vs RV32IMC); paths to read first; a binary done check;
what to leave for the parent (commit only if asked; no drive-by refactors).

This repo’s MCP spawn path **supersedes** the copy-paste / “operator says Codex
finished” handoff in that user rule. Keep writing `.codex/lean-handoff.md` as the
canonical brief; chat-only fences are not the sole copy.
