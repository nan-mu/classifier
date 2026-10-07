# Classifier Lean slice

Architecture-agnostic math in `CommonMath/`. RV32IMC decode and Expr value
functions in `LeanRV32IMC/`. Rust `lean_bridge` links Lake shared libraries.

```bash
lake build
cargo test --manifest-path lean_bridge/Cargo.toml
```

Toolchain: Lean 4.29.0. After layout changes: **Lean 4: Restart Server**.
