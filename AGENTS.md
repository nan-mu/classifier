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
RV32IMC.lean                    imports Insn + Encode + Expr
RV32IMC/Insn.lean               decoded Insn + field tags
RV32IMC/Encode.lean             encode / encodeCompressed
RV32IMC/Expr.lean               expr / step (+ FFI smoke exports)
lean_bridge/                    Rust FFI to Lean @[export]s (incl. demoSnapshot)
debug_server/                   axum §18 Expand debug API (Lean-backed via lean_bridge)
debug_web/                      Vite + Kuma UI + xyflow canvas for that API
xtask/                          `cargo xtask demo` one-shot launcher
doc/common-math.md
doc/rv32imc-expr-value-functions.md
```

## Build & check

```bash
lake build
lake build RV32IMC
cargo test -p lean_bridge
cargo test -p debug_server
cargo xtask demo   # lake build + debug_server :8788 + Vite :5173 (Ctrl-C stops both)
```

Toolchain: `leanprover/lean4:v4.29.0`. After layout changes: **Lean 4: Restart Server**.

## Lean via Codex

Lean4 implementation routes through user Cursor rule `lean-via-codex` +
`python3 ~/.cursor/scripts/codex-quota-gate.py --json`: Codex CLI `-m gpt-6.1-sol`
via `~/.cursor/scripts/codex-lean-exec.sh` (`--approve-for-me`, stdin closed)
only when 5h and weekly remaining are both **> 50%**; otherwise Cursor auto
subagents. Never redeem Codex reset credits unless the operator asks. Do not
use removed `--full-auto`.
