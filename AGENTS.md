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
CommonMath/{Bits,Reg,Numeric,Op,Term,Expr,Direction,Insn,Path,Expand,Demo,Ffi}.lean
RV32IMC.lean                    imports Insn + Encode + Expr
RV32IMC/Insn.lean               decoded Insn + field tags
RV32IMC/Encode.lean             encode / encodeCompressed
RV32IMC/Expr.lean               expr / step (+ FFI smoke exports)
lean_bridge/                    Rust FFI to Lean @[export]s (incl. demoSnapshot)
debug_server/                   axum §18 Expand debug API (Lean-backed via lean_bridge)
debug_web/                      Vite + Kuma UI + xyflow canvas for that API
doc/common-math.md
doc/rv32imc-expr-value-functions.md
```

## Build & check

```bash
lake build
lake build RV32IMC
cargo test --manifest-path lean_bridge/Cargo.toml
cargo test --manifest-path debug_server/Cargo.toml
# debug UI: cargo run --manifest-path debug_server/Cargo.toml
#            then cd debug_web && npm install && npm run dev  (http://127.0.0.1:5173)
```

Toolchain: `leanprover/lean4:v4.29.0`. After layout changes: **Lean 4: Restart Server**.
