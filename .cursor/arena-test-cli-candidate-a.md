# Candidate A — process-isolated command envelope

`classifier_domain` owns in-memory expand and compare-tree. The CLI is a
one-shot adapter over a caller-owned session directory. The harness
interprets `CaseSpec` by spawning that CLI and does not link the domain crate.

## Usage sketch

Workspace root is `tooling/`. Binary names: `classifier`, `classifier-harness`.
`server` stays the HTTP binary (`lake run dev` unchanged).

```bash
classifier create --state "$WORK" --arch rv32imc --budget 1024 \
  --image tooling/test/xdp/just_tx/just_tx.elf
classifier run --state "$WORK" --id 1
classifier compare-tree --left /tmp/rv.json --right /tmp/bpf.json
classifier-harness --root tooling/test --cli ./target/debug/classifier
```

Stdout is one JSON object. Exit **0** means `"ok": true`. Exit **1** means
`"ok": false` and an `error` object (bad image, unknown id). Exit **2** is
usage (`error.code = "usage"`). A fresh `--state` directory holds opaque
`<id>.session.json` files plus `next_id`. `create` allocates the id, writes
the file, prints the snapshot. `run` loads that file, calls `run_all`, writes
it back. `compare-tree` reads two snapshot JSON files (HTTP `left`/`right`
shape) and does not touch `--state`.

A case is `tooling/test/{base,xdp,fail}/<id>/case.json` plus copied ELF
assets beside it. Harness walk: for each `steps[]` entry, spawn one CLI
command; remember `bind → last envelope`; on `compare_tree`, write each
bind's `.data` to a temp file and pass those paths. Then apply `expect`
and `assert` to the last envelope.

```json
{
  "id": "just_tx",
  "suite": "xdp",
  "budget": 1024,
  "artifacts": { "rv32": "just_tx.elf", "ebpf": "just_tx.bpf.o" },
  "steps": [
    { "op": "create", "bind": "rv", "arch": "rv32imc", "artifact": "rv32" },
    { "op": "run", "bind": "rv" },
    { "op": "create", "bind": "bpf", "arch": "ebpf", "artifact": "ebpf", "map_elf": "rv32" },
    { "op": "run", "bind": "bpf" },
    { "op": "compare_tree", "left": "rv", "right": "bpf" }
  ],
  "expect": { "kind": "pass", "status": "complete", "compare_tree": { "fail": 0 } },
  "assert": [{ "path": "$.data.status", "eq": "pass" }]
}
```

`map_elf` names the other case-dir artifact. CLI passes those bytes into the
existing eBPF filler (`ebpf::Meta::just_tx_product` plus map rows from
`parse_xdp_elf`). Omitted `map_elf` keeps today's embedded `just_tx` maps.
`base` cases use the same file shape with `"suite": "base"` and `"kind": "pass"`.

## Crate/module map

```text
tooling/Cargo.toml                 members += domain, cli, harness
tooling/domain/                    package classifier-domain, lib classifier_domain
  src/lib.rs                       re-exports below; pred_match and image parsers stay private
  src/{expand,engine,pred_tree,rv32_image,bpf_image,ebpf_disasm}.rs
  src/driver/                      moved as-is, not re-exported
  src/pred_match.rs                pub(crate), called only from pred_tree
tooling/server/src/main.rs        axum, in-memory id map, /run/ws
tooling/cli/src/main.rs           manual argv (no clap) → domain → envelope
tooling/harness/src/main.rs       CaseSpec walk; std::process + serde_json only
tooling/lean-binding/             unchanged FFI
tooling/test/base|xdp|fail/<id>/  case.json + copied .elf / .bpf.o
```

Deps that move with the modules: `lean-binding`, `xpost-elf`, `riscv-isa`.
`server` keeps axum, tokio, tower-http, base64. `cli` depends on domain.
`harness` depends on neither domain nor axum.

## Public types and function signatures

```rust
// classifier_domain — called on an InferencePool worker, as Session::new is today
pub struct OpenReq {
    pub id: String,
    pub arch: Arch,
    pub budget: u32,
    pub name: String,
    pub bytes: Vec<u8>,
    pub map_elf: Option<Vec<u8>>,
}
pub enum DomainError { BadArch, BadImage(String), Pool(PoolError) }

impl Session {
    pub fn open(req: OpenReq) -> Result<Self, DomainError> { not implemented }
    pub fn step_once(&mut self) -> Snapshot { not implemented }
    pub fn run_all(&mut self) -> Snapshot { not implemented }
    pub fn drive_batch(&mut self, policy: WaveBatchPolicy) -> BatchTick { not implemented }
    pub fn snapshot(&self) -> Snapshot { not implemented }
}
pub fn compare_tree(left: &SnapRun, right: &SnapRun) -> TreeReport { not implemented }

// cli
fn emit(cmd: &str, result: Result<serde_json::Value, DomainError>) -> i32 { not implemented }

// harness
pub fn interpret(spec: &CaseSpec, cli: &Path, state: &Path) -> Result<(), Fail> { not implemented }
```

`Arch`, `Snapshot`, `SnapRun`, `TreeReport`, `WaveBatchPolicy`, `BatchTick`,
and `InferencePool` move unchanged. Server `/run/ws` still calls `drive_batch`.
CLI `run` calls `run_all`. `CaseSpec` is a harness serde type, not a domain type.
No new Lean FFI.

Envelope (CLI stdout):

```json
{ "ok": true, "cmd": "run", "id": "1", "data": { } }
{ "ok": false, "cmd": "create", "error": { "code": "bad_image", "message": "..." } }
```

## CaseSpec JSON schema example

`fail` suite, fuel-exhaustion on copied `just_tx.elf` (budget 512):

```json
{
  "id": "short_budget",
  "suite": "fail",
  "budget": 512,
  "artifacts": { "rv32": "just_tx.elf" },
  "steps": [
    { "op": "create", "bind": "s", "arch": "rv32imc", "artifact": "rv32" },
    { "op": "run", "bind": "s" }
  ],
  "expect": { "kind": "fail", "status": "fail" },
  "assert": [{ "path": "$.data.reason", "eq": "LimitExceeded" }]
}
```

| Field | Rule |
| --- | --- |
| `suite` | `base` \| `xdp` \| `fail`. Selects the directory only. |
| `expect.kind` | `pass`: exit 0. `fail`: exit 0, session `status` or compare-tree failures are the intended outcome. `error`: exit 1 and `error`. |
| `expect.status` | Optional `complete` \| `fail` on the last create/run `.data.status`. |
| `expect.compare_tree` | `{ "fail": 0 }` exact, or `{ "fail_at_least": 1 }`. Count is `data.nodes[].matchStatus == "fail"`. |
| `assert[]` | Last envelope. `{path, eq}` or `{path, len}` or `{path, exists: true}`. Dotted `$.data…` only. |
| `steps[].op` | `create` \| `run` \| `compare_tree`. Unknown op or suite is a harness error. |

`expect.http` is not read on this path. An `error` case sets `expect.kind`
to `error` and checks `$.error.code`.

## Migration steps from current fat server

1. Add `tooling/domain`. Move `expand`, `engine`, `pred_tree`, `pred_match`,
   `rv32_image`, `bpf_image`, `ebpf_disasm`, and `driver/` out of `server/src`.
2. Collapse `Session::new` / `new_ebpf` into `Session::open`. Keep image
   parsers crate-private; surface parse failure as `DomainError::BadImage`.
3. Leave `server/src/main.rs` as axum only: `CreateBody` → `OpenReq`, same
   routes, in-memory map, ws loop, embedded fixtures for an empty POST.
4. Add `cli`. Persist serde of the Rust `Session` (insns, meta, agenda, fuel,
   graph JSON). The next process calls the existing create/step/merge strings.
5. Copy `/Volumes/SSD/bs/build/<prog>/{<prog>.elf,bpf.o}` and the ELFs already
   in `tooling/fixtures/` into `tooling/test/`. xdp ids: `just_tx`, `just_drop`,
   `merge_try`, `xdp`. `base` holds API and branch/loop predicate cases;
   `fail` holds reject, `status: fail`, and `fail_at_least` compare cases.
6. Add `harness`. Extend `tooling/scripts/rust-ci.sh` fmt/clippy members with
   `domain`, `cli`, `harness`. Leave `lean-binding` and HTTP paths as they are.
   Drop the in-crate short-budget HTTP test only after `fail/short_budget` passes.

## Alternatives considered and rejected

- **In-process `#[test]` calling `Session`.** The suite would not lock the JSON
  CLI contract.
- **`classifier test` inside the CLI crate.** A second interpreter next to
  HTTP, and `CaseSpec` would leak into the library.
- **One binary with `--http` versus subcommands.** Every case spawn links axum,
  and fixtures stay `include_bytes!`.
- **Harness as an HTTP client of `server`.** Port binding in CI, and exit-code
  `error` cases have no HTTP twin (`expect.http` stays a server concern).
- **`base.rs` / `xdp.rs` / `fail.rs` modules.** Per-suite branches instead of
  one walk over `CaseSpec`.

## Rationale

Create, run, and compare-tree already exist as Rust functions beside axum.
Putting them in `classifier_domain` with `Session::open`, `run_all`,
`drive_batch`, and `compare_tree` is enough for the HTTP server and the CLI.
Envelope, exit codes, and `CaseSpec` stay in the adapters, so the library
does not gain a test DSL.

The harness is a pure interpreter: one `op` enum, one bind map, one expect
check. Suite directories differ by data. Spawning the CLI makes a missing
flag or a non-JSON stdout a failed case.

Session files hold Rust-owned graph state. Lean stays stateless across
processes and is entered only through the current create/step/merge FFI.
Copied ELF bytes let a case change without rebuilding `server`. eBPF map
rows remain an input to the existing product-meta filler.
