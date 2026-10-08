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
doc/rv32-initial-expr.zh.md     RV32 entry E0 spec
lean_binding/                   Rust FFI binding to Lean @[export]s (incl. demoSnapshot)
debug_server/                   axum §18 Expand debug API (Lean-backed via lean_binding)
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

## Lean4 via user Codex

Lean4 implementation/questions: follow user Cursor rule `lean4-codex-handoff`.
Main agent does not edit Lean or call Codex CLI. After the operator reports Codex
finished (often with no details), the main agent verifies via git + `lake` / tests.

### Codex handoff file

Write the full copy-pastable Codex / Task brief to a **gitignored** file under
`.codex/` (directory is in `.gitignore`). Prefer a stable name such as
`.codex/lean-handoff.md` (overwrite per task). Tell the operator the path; do not
rely on chat-only fences as the sole copy of the prompt. Never commit `.codex/`.
