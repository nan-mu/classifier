# RV32IMC Lean slice

Lean modules implement classifier mathematics and RV32IMC Expr value functions.
Rust `lean_bridge` links the Lake shared libraries and runs the tests.

```bash
lake build
cargo test --manifest-path lean_bridge/Cargo.toml
```

| Module | Role |
|---|---|
| `CommonMath.lean` | Reg, Term, Expr, solve, shared numeric ops |
| `LeanRV32IMC/Types.lean` | Instruction inductive (Sail constructor names) |
| `LeanRV32IMC/Decode.lean` | Decode |
| `LeanRV32IMC/Value.lean` | `value(Eg, i)` |
| `lean_bridge/` | Rust FFI + tests |

Toolchain: `lean-toolchain` → Lean 4.29.0. After layout changes: **Lean 4: Restart Server**.
