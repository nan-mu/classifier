# Server

[项目入口](../../README.md) · [文档索引](../../doc/README.md)

HTTP session chrome for budgeted Expand. Expand graphs and SemState
`exprs` / `predicates` come from Lean `rv32Snapshot` via the `lean-binding` crate.
Instruction list text is partitioned at runtime from the session firmware bytes
with the `riscv-isa` crate (strict RV32IMC 2/4-byte lengths). When the client
omits an image, the server uses `tooling/fixtures/esp32c3.bin`. Regenerate
`RV32IMC/Esp32c3Program.lean` with
`UPDATE_ESP32C3_LEAN=1 lake env cargo test --manifest-path tooling/Cargo.toml -p server lean_words`.
This crate keeps session id, step count, focus, and the append-only log. It does
not reimplement Expand.

## Run

From the repository root:

```bash
lake run dev
```

To run only the server from the repository root:

```bash
lake build server
lake env cargo run --manifest-path tooling/Cargo.toml -p server
```

The process listens on `http://127.0.0.1:8788` by default. Set `PORT` to override.

## Routes

`POST /api/session` accepts:

```json
{
  "arch": "rv32imc",
  "budget": 512,
  "name": "esp32c3.bin",
  "image_b64": null
}
```

- `arch` is currently only `rv32imc` (alias `esp32c3` accepted). Default `rv32imc`.
- `budget` defaults to 512.
- `name` is a display label; default `esp32c3.bin`.
- `image_b64` is optional base64 firmware. Omitted or empty → embedded
  `tooling/fixtures/esp32c3.bin`. Rejected when empty after decode or larger than 256 KiB.

`POST /api/session/<id>/step` advances the Lean step counter by one and refreshes.

`POST /api/session/<id>/run` steps until status is `complete` or `fail` (cap `budget+1`).

`GET /api/session/<id>` returns the current snapshot.

The ESP32-C3 fixture has separate binding and target-resolution limits; a larger
budget does not guarantee completion. Current observations are documented in
[RV32IMC value functions, section 7.4](../../doc/rv32imc-expr-value-functions.md).
