# debug_web

Canvas for the Expand demo. Vite proxies `/api` to the mock server.

## Run

Start `debug_server` first. Then, from `debug_web`, run:

```bash
npm install
npm run dev
```

Open `http://127.0.0.1:5173`.

`npm run build` typechecks the app and writes `dist/`.

Click a node to focus it. Click the focused work-head node again, or press **单步调试**, to expand that node. **到底调试** runs until the session is complete or failed.
