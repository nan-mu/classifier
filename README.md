# RV32IMC Lean slice

Single module: `LeanRV32IMC.lean` (types + instruction + decode + execute stubs).

```bash
lake build
python3 test_esp32c3.py   # decode_imc.py + esp32c3.bin
```

Toolchain: `lean-toolchain` → Lean 4.29.0. After layout changes: **Lean 4: Restart Server**.
