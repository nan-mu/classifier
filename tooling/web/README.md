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

The node panel groups expressions by `RegKind` (Real / Stack / Map / Packet),
shows arrival and expansion deltas (`eiIn` / `eiOut`), labels comparison Expr
constraints, and expands ret / helper Predicates with term trees. Packet alphas decode to `(κ, offset)`. Graph
nodes mark helper (`H`), packet (`Pk`), and return (`R`) presence.

```bash
npm --prefix tooling/web test
```

runs Vitest unit checks for register/term parsing and Predicate formatting.

The UI starts with architecture `RV32`, compact XDP ELF `just_tx.elf` (server
default), and budget 1024. Choose a local `.elf` file in xpost's Compact ELF V0
format, then press **新建运行** to upload it. Generic firmware ELF and raw BIN
files are rejected. Press **恢复默认** and **新建运行** to use the embedded
fixture again. API fields and helper limitations are documented in
[Server](../server/README.md).
