# debug_server

[项目入口](../README.md) · [文档索引](../doc/README.md)

HTTP session chrome for the section 18 Expand demo. Expand graphs and SemState
`exprs` / `predicates` come from Lean `rv32Snapshot` via `lean_binding`. Instruction
list text is partitioned at runtime from repo-root `esp32c3.bin` with the
`riscv-isa` crate (strict RV32IMC 2/4-byte lengths). Regenerate
`RV32IMC/Esp32c3Program.lean` with
`UPDATE_ESP32C3_LEAN=1 cargo test -p debug_server lean_words`.
This crate keeps session id, step count, focus, and the append-only log. It does
not reimplement Expand.

## Run

From the repo root (preferred):

```bash
cargo xtask demo
```

Or from `debug_server`:

```bash
cargo run
```

The process listens on `http://127.0.0.1:8788` by default. Set `PORT` to override.

## Routes

`POST /api/session` accepts `{"program":"esp32c3","budget":512}`.
`program` is `esp32c3` (default) or `demo`; omitted budget defaults to 11.
For the section 18 bounded-loop example, use `{"program":"demo","budget":11}`.

`POST /api/session/<id>/step` advances the Lean step counter by one and refreshes.

`POST /api/session/<id>/run` steps until status is `complete` or `fail` (cap `budget+1`).

`GET /api/session/<id>` returns the current snapshot.

For `program: "demo"`, budget 11 ends as `complete` with an Exit node and fuel 0. Budget 10 ends as `fail` with reason `LimitExceeded`, and the return node is still in `work`.

The ESP32-C3 image has separate binding and target-resolution limits; a larger
budget does not guarantee completion. Current observations are documented in
[RV32IMC value functions, section 7.4](../doc/rv32imc-expr-value-functions.md).
