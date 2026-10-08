# debug_server

Mock HTTP server for the section 18 Expand demo. Sessions stay in memory. This crate does not call Lean.

## Run

From `debug_server`, run:

```bash
cargo run
```

The process listens on `http://127.0.0.1:8788` by default. Set `PORT` to override.

## Routes

`POST /api/session` accepts `{"budget": 11}`. An empty object uses budget 11.

`POST /api/session/<id>/step` runs one Expand iteration.

`POST /api/session/<id>/run` runs until the status is `complete` or `fail`.

`GET /api/session/<id>` returns the current snapshot.

Budget 11 ends as `complete` with an Exit node and fuel 0. Budget 10 ends as `fail` with reason `LimitExceeded`, and the return node is still in `work`.
