# Classifier repository guide for AI agents

Lean4 classifier mathematics and RV32IMC decode/value. Architecture-agnostic
structures live under `CommonMath/`; RV32IMC is one concrete ISA layer.

## Working conventions

- Use concise prose or lists, not tables, when writing Markdown plans for this user.
- Ground changes in Lean sources and `lean_bridge` Rust FFI tests.
- Keep ISA-specific rules (x0, RV32M div overflow, Sail constructors) out of `CommonMath`.
- LOAD/STORE virtual-mark matching may still return `none`; do not call that finished.

## Layout

```text
CommonMath/
  Bits.lean      Width, InsnWidth, M/s/u
  Reg.lean       RegKind, Reg (alpha is arch-assigned)
  Numeric.lean   §7 named numeric functions
  Op.lean        form operators + interpretOp
  Term.lean      Term, FV, eval, solve, *Star
  Expr.lean      Rel, Expr, ExprSet, override, interpretExpr
  Insn.lean      Insn, Predicate/InstNext stubs, HistoryItem
  Ffi.lean       @[export] numeric smoke tests
LeanRV32IMC/
  Types.lean     instruction inductive (Sail names)
  Decode.lean    encdec_*
  Regs.lean      x0/ra/sp/pc → CommonMath.Reg
  MArith.lean    RV32M mulh/div/rem rules
  Value.lean     value(Eg, i) using CommonMath Expr
  Ffi.lean       decode/value/ExprSet exports
lean_bridge/     Rust FFI + cargo test
doc/common-math.md
doc/rv32imc-expr-value-functions.md
```

## Build & check

```bash
lake build
cargo test --manifest-path lean_bridge/Cargo.toml
```

Toolchain: `lean-toolchain` → Lean 4.29.0. After layout changes: **Lean 4: Restart Server**.

## Scope

CommonMath models `doc/common-math.md` (Reg/Term/Expr/solve/history shells).
LeanRV32IMC adds decode plus Expr value functions for I/M/Zca.
Predicate payloads and InstNext structure remain TBD.
