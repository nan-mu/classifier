# Classifier repository guide for AI agents

Lean4 RV32IMC slice for ESP32-C3 XDP native code. The former Rust
prefixgen/pathgen/QF_BV host classifier and Rocq models have been removed;
work proceeds in Lean4 first.

## Working conventions

- Use concise prose or lists, not tables, when writing Markdown plans for this user.
- Ground changes in the checked-out Lean sources and the Python decode fixture.
- Keep changes scoped to the requested task. Do not reintroduce the deleted
  Rust/Rocq classifier stack unless the user asks.
- Incomplete Sail runtime pieces may use `def_wanted`; do not describe axioms
  or unfinished execute stubs as completed proofs.

## Layout

```text
LeanRV32IMC.lean   single-module types + instruction + decode + execute stubs
lakefile.toml      Lake package (lib LeanRV32IMC)
lean-toolchain     leanprover/lean4:v4.29.0
decode_imc.py      RV32IMC decode helper (fixture check)
test_esp32c3.py    decode against esp32c3.bin
esp32c3.bin        tiny decode fixture
README.md          human-facing notes
.vscode/           Lean4 editor PATH for elan
```

## Build & check

```bash
lake build
python3 test_esp32c3.py
```

Requires `elan` with toolchain `leanprover/lean4:v4.29.0` (see `lean-toolchain`).
After layout changes: **Lean 4: Restart Server**.

## Scope

Kept in the Lean module: RV32 base I, M (`MUL`/`DIV`/`REM`), and Zca compressed
ops used on RV32.

Dropped from the full Sail Lean_RV32D model: RV64 `*W` / `C_*W` / `C_LD*`,
Zcb, A/F/D/V, crypto, and other extensions.

Execute still carries Sail-shaped signatures; unfinished runtime uses
`def_wanted`.
