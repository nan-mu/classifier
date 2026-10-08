# debug_web

[项目入口](../README.md) · [文档索引](../doc/README.md)

Canvas for the Expand demo. Vite proxies `/api` to the Lean-backed debug server.

## Run

From the repo root (preferred):

```bash
cargo xtask demo
```

Or start pieces by hand: run `debug_server`, then from `debug_web`:

```bash
npm install
npm run dev
```

Open `http://127.0.0.1:5173`.

`npm run build` typechecks the app and writes `dist/`.

Click a node to focus it. Click the focused work-head node again, or press **单步调试**, to expand that node. **到底调试** runs until the session is complete or failed.

The UI starts with `esp32c3` and budget 512. The program selector also offers
the section 18 `demo`; its budget 11 example completes. API request defaults
are documented in [debug_server](../debug_server/README.md).
