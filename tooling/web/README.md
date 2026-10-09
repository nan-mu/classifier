# Web

[项目入口](../../README.md) · [文档索引](../../doc/README.md)

Canvas for budgeted Expand. Vite proxies `/api` to the Lean-backed server.

## Run

From the repository root:

```bash
lake run dev
```

To run only the frontend after starting the server, use the repository root:

```bash
lake build web
lake env npm --prefix tooling/web run dev
```

Open `http://127.0.0.1:5173`.

`npm run build` typechecks the app and writes `dist/`.

Click a node to focus it. Click the focused work-head node again, or press **单步调试**, to expand that node. **到底调试** runs until the session is complete or failed.

The UI starts with architecture `RV32IMC`, firmware `esp32c3.bin` (server default),
and budget 512. Choose a local firmware file to upload; leave the file empty or
press **恢复默认** to use the embedded fixture. API fields are documented in
[Server](../server/README.md).
