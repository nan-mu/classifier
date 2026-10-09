# Classifier repository guide for AI agents

## Architecture

`CommonMath` owns architecture-agnostic Reg / Term / Expr / solve / history
shells. Read `doc/common-math.md` before changing shared math.

`RV32IMC` is a thin ISA layer. It defines decoded `Insn`,
`encode` / `encodeCompressed` (bits → Insn), and
`expr` (ExprSet × Insn ⇀ ExprSet).

RV32 uses `CommonMath.Reg`, `Term`, and `ExprSet`. Keep shared math and register
ADTs in `CommonMath`. Do not add Sail execute stubs to `RV32IMC`.

## Layout

The repository root is the Lean workspace. Non-Lean tools live in `tooling/`.

```text
CommonMath.lean                 shared math root reexports
CommonMath/                     shared objects, paths, expansion, rendering, FFI exports
RV32IMC.lean                    imports Insn + Encode + Expr + Initial + Expand
RV32IMC/Insn.lean               decoded instructions and field tags
RV32IMC/Encode.lean             encode / encodeCompressed
RV32IMC/Expr.lean               expr / step and FFI smoke exports
RV32IMC/Initial.lean            EntryParams + E0 (real ∪ xdp_md SW slots)
RV32IMC/Expand.lean             rv32Step / rv32Snapshot and snapshot export
RV32IMC/Esp32c3Program.lean     generated instruction words for the ESP32-C3 fixture
EBPF.lean, EBPF/                eBPF instruction and expression modules
lakefile.lean, lean-toolchain   Lean package and pinned toolchain
doc/                           Lean specifications and research notes
tooling/Cargo.toml              Rust workspace, with one shared Cargo.lock
tooling/lean-binding/           Rust FFI binding to Lean exports
tooling/server/                 axum Expand API, instruction text via riscv-isa
tooling/web/                    Vite, Kuma UI, and xyflow canvas
tooling/scripts/dev.py          development service lifecycle, invoked by Lake
tooling/fixtures/esp32c3.bin    XDP image used by the server and generated Lean words
tooling/scripts/smoke.py        live API checks and migration snapshot comparison
```

## Build and check

Run these commands from the repository root.

```bash
lake build
lake test
```

Start both services from the repository root.

```bash
lake run dev
```

`lake build` builds Lean shared libraries, the Rust server, and the web app.
`lake test` runs Rust tests, the web build, and live API checks.
`lake run dev` builds the server, installs frontend dependencies, and starts
the API on `8788` and Vite on `5173`. Ctrl-C stops both services.
Use Lake as the project entrypoint. Cargo and npm are component build tools.

Toolchain is `leanprover/lean4:v4.29.0`. After Lean layout changes, run
**Lean 4: Restart Server** in the editor.

## Codex model policy

Use only `gpt-6.1-sol` for Codex tasks and subagents, including pstack profiles.
Use only `low`, `medium`, or `high` reasoning effort. Keep a lower effort when
suitable. Do not use `xhigh`, `max`, `ultra`, the Fast speed tier, or automatic
model fallback. If the permitted model is unavailable, report the limitation.

Preserve this policy when updating or reinstalling pstack custom-agent profiles.
Change it only when the user explicitly revises it.

## Recommended workflow for Cursor Auto

This section recommends settings and delegation for a **Cursor Auto main
agent**. It does not require native Codex sessions to invoke MCP or delegate
Lean work. Native Codex sessions may edit Lean and FFI sources and run builds
directly under the architecture and model policies above.

- Prefer Cursor Auto for the parent chat and Cursor Task subagents. Omit the
  Task model or use `inherit`. Use `auto` for Cursor pstack roles. Avoid pinning
  paid Cursor Task model slugs solely for Lean work.
- For Lean work, prefer the Cursor MCP namespace `user-codex-subagent` with
  `gpt-6.1-sol`. This includes Lean sources, Lake configuration, theorem work,
  builds, and FFI that exposes Lean exports.
- Defaults are maintained in `~/.codex/config.toml` and
  `~/.cursor/rules/model-access.mdc`. Do not reset settings to bypass caps.

When using this MCP delegation path:

1. Write a self-contained brief to `.codex/lean-handoff.md`. This directory is
   gitignored. Never commit `.codex/`.
2. Include the absolute repository root and cwd, goal, architecture constraints,
   files to read first, pass/fail checks, and deliverables. Do not commit unless
   asked. Do not include unrelated refactors.
3. Call `user-codex-subagent` → `spawn_agent` with the brief as `prompt`.
   For independent Lean tasks, use `spawn_agents_parallel` with one prompt per
   task. Give each writer separate file ownership.
4. Inspect `git status` and `git diff`, then run the brief's build and test
   checks. Continue from that evidence. Rust, TS, and documentation work can
   proceed independently when it does not depend on unfinished Lean APIs.

If this MCP is unavailable in Cursor, report the limitation and choose an
available execution path with the user. The file-backed MCP brief replaces the
older copy-paste or operator-reported completion handoff for this workflow.
