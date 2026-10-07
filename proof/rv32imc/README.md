# RV32IMC Lean slice

Single module: `LeanRV32IMC.lean` (types + instruction + decode + execute stubs).

Repo root Lake wrapper (`srcDir = "proof/rv32imc"`) lets the editor resolve
`import LeanRV32IMC`. After layout changes: **Lean 4: Restart Server**.

```bash
cd proof/rv32imc && lake build
python3 test_esp32c3.py   # decode_imc.py + esp32c3.bin
```
