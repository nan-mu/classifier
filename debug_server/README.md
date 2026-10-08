# debug_server

HTTP session chrome for the section 18 Expand demo. Expand graphs come from Lean
`demoSnapshot` via `lean_bridge`. This crate keeps session id, step count, focus,
and the append-only log. It does not reimplement Expand.

## Run

From `debug_server`, run:

```bash
cargo run
```

The process listens on `http://127.0.0.1:8788` by default. Set `PORT` to override.

## Routes

`POST /api/session` accepts `{"budget": 11}`. An empty object uses budget 11.

`POST /api/session/<id>/step` advances the Lean step counter by one and refreshes.

`POST /api/session/<id>/run` steps until status is `complete` or `fail` (cap `budget+1`).

`GET /api/session/<id>` returns the current snapshot.

Budget 11 ends as `complete` with an Exit node and fuel 0. Budget 10 ends as `fail` with reason `LimitExceeded`, and the return node is still in `work`.
