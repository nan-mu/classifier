# Classifier repository guide for AI agents

Lean4 RV32IMC slice for ESP32-C3 XDP native code. Sail execute stubs are gone.
Shared mathematics and Expr value functions follow `doc/common-math.md` and
`doc/rv32imc-expr-value-functions.md`.

## Working conventions

- Use concise prose or lists, not tables, when writing Markdown plans for this user.
- Ground changes in the checked-out Lean sources and the Rust `lean_bridge` tests.
- Keep changes scoped to the requested task. Do not reintroduce the deleted
  Rust/Rocq classifier stack under `src/` unless the user asks.
- Incomplete Predicate / virtual-mark matching may return `none` (reject); do not
  describe those TBD rules as completed proofs.

## Layout

```text
CommonMath.lean              shared Reg/Term/Expr/solve/numeric ops
LeanRV32IMC.lean             root imports
LeanRV32IMC/Types.lean       regidx, op tags, instruction
LeanRV32IMC/Decode.lean      encdec_backwards / compressed
LeanRV32IMC/Value.lean       value(Eg, i) Expr value functions
LeanRV32IMC/Ffi.lean         @[export] C ABI for Rust
lean_bridge/                 Rust crate: FFI + cargo test
doc/common-math.md           math definitions
doc/rv32imc-expr-value-functions.md
lakefile.toml                Lake libs (shared facets)
lean-toolchain               leanprover/lean4:v4.29.0
```

## Build & check

```bash
lake build
cargo test --manifest-path lean_bridge/Cargo.toml
```

Requires `elan` with toolchain `leanprover/lean4:v4.29.0` and a Rust toolchain.
`lean_bridge/build.rs` runs `lake build` and links the Lake shared libraries.
After Lean layout changes: **Lean 4: Restart Server**.

## Scope

Kept in Lean: RV32 base I, M (`MUL`/`DIV`/`REM`), and Zca compressed ops used on RV32.

Dropped from the full Sail Lean_RV32D model: RV64 `*W` / `C_*W` / `C_LD*`,
Zcb, A/F/D/V, crypto, and other extensions.

`value` returns `Option ExprSet` (`none` = reject, `some []` = success with no new Expr).
LOAD/STORE virtual-mark matching is TBD and currently rejects.
SailM / ExecutionResult / `def_wanted` execute stubs are not part of this tree.
