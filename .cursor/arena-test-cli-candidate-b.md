# Arena candidate B: command reducer kernel

**Organizing idea:** `classifier-kernel` exposes `Kernel::execute(Command) -> Envelope`. Server, JSON CLI, and CaseSpec harness are adapters on one command vocabulary—not a renamed fat binary.

## Usage sketch

```bash
# Offline JSON CLI (one command per line on stdin, one Envelope per line on stdout)
echo '{"v":1,"cmd":{"Create":{"arch":"rv32imc","budget":1024,"image":{"fixture":"just_tx"}}}}' \
  | classifier-cli

# Run full declared suite; harness writes a JSON report (exit 0 iff all cases pass)
classifier-test --workspace tooling --report /tmp/classifier-report.json

# HTTP unchanged for the web UI; routes map 1:1 to Command variants
lake run dev   # server :8788 still serves /api/session, /api/compare/tree, …
```

Harness layout (workspace-relative):

```text
tooling/test/
  base/…/case.json
  xdp/{just_tx,just_drop,merge_try,firewall}/case.json + copied *.elf / *.bpf.o
  fail/…/case.json
```

Copy XDP pairs once from `bs/build/<prog>/` into `tooling/test/xdp/<prog>/` (firewall: `xdp.elf` + `bpf.o` in CaseSpec).

## Crate/module map

| Crate | Role |
| --- | --- |
| `classifier-kernel` | `Command`, `Envelope`, `Kernel`, session store, expand/compare dispatch (moved from today’s `server/src/{expand,engine,driver,pred_*,rv32_image,bpf_image}`) |
| `classifier-cli` | Binary: NDJSON command loop → `Kernel::execute` → NDJSON envelopes |
| `server` | Axum only: HTTP body → `Command`, `Envelope` → status + JSON body; WS `Run` streams `Envelope` with `event: Step` |
| `classifier-harness` | `CaseSpec` types + interpreter; depends on `classifier-kernel` (in-process, no shell) |
| `lean-binding` | Unchanged FFI surface |

```text
tooling/
  classifier-kernel/src/
    command.rs      Command enum + JSON (de)schema
    envelope.rs     Envelope, ErrorCode, payload slots
    kernel.rs       Kernel + SessionStore + InferencePool wiring
    expand/         Session, engine, driver (from server)
    compare/        pred_tree, pred_match helpers
    image/          rv32 + ebpf load (fixtures + path bytes)
  classifier-cli/src/main.rs
  classifier-harness/src/{spec,interp,assert,report}.rs
  server/src/main.rs          HTTP adapter only
  test/{base,xdp,fail}/       CaseSpec + artifacts
```

## Public types and function signatures

```rust
// classifier-kernel — sole product domain API

pub struct Kernel {
    sessions: SessionStore,
    pool: InferencePool,
    fixtures: FixtureTable, // embedded + optional workspace overlay for tests
}

pub enum Command {
    Create { arch: Arch, budget: u32, image: ImageSource, name: Option<String> },
    Step { session_id: SessionId },
    Run { session_id: SessionId, until: RunUntil }, // Complete | BudgetExhausted
    Get { session_id: SessionId },
    CompareRuns { left: SnapshotRef, right: SnapshotRef },
    ComparePredicates { left: SnapshotRef, right: SnapshotRef },
    CompareTree { left: SnapshotRef, right: SnapshotRef },
    Shutdown, // CLI/harness only; no-op for server lifetime
}

pub enum ImageSource {
    Fixture(&'static str),
    Bytes(Vec<u8>),
    Path { path: PathBuf }, // harness + CLI; server may reject or allow via env flag
}

pub enum SnapshotRef {
    Inline(Value),           // full snapshot JSON
    Session { id: SessionId }, // last materialized snapshot
}

#[derive(Serialize)]
pub struct Envelope {
    pub v: u32,
    pub ok: bool,
    pub command: &'static str,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub session_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub payload: Option<Value>,   // Snapshot, compare tree, matchStatus, …
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<KernelError>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub event: Option<&'static str>, // "step" | "done" for streamed Run
}

impl Kernel {
    pub fn new(config: KernelConfig) -> Self { unimplemented!() }
    pub async fn execute(&self, cmd: Command) -> Envelope { unimplemented!() }
    pub async fn execute_run_stream(
        &self,
        session_id: SessionId,
    ) -> impl Stream<Item = Envelope> { unimplemented!() }
}

// classifier-harness

pub struct CaseSpec { /* see schema below */ }

pub fn run_suite(workspace: &Path, suite: SuiteFilter, report: &mut Report) -> ExitStatus {
    unimplemented!()
}

pub fn run_case(kernel: &Kernel, spec: &CaseSpec, case_dir: &Path) -> CaseOutcome {
    unimplemented!()
}
```

**Public surface rule:** downstream crates import `classifier_kernel::{Kernel, Command, Envelope, Arch}` only. Compare tree shapes stay serde `Value` inside `payload` (same JSON the UI already consumes).

## CaseSpec JSON schema example

```json
{
  "id": "xdp.just_tx.dual_compare",
  "suite": "xdp",
  "dir": "xdp/just_tx",
  "expect": { "kind": "pass", "compare_tree": { "fail": 0 } },
  "budget": 1024,
  "steps": [
    {
      "send": {
        "cmd": {
          "Create": {
            "arch": "rv32imc",
            "budget": 1024,
            "image": { "path": "just_tx.elf" }
          }
        }
      },
      "bind": { "session": "rv32" }
    },
    {
      "send": {
        "cmd": {
          "Create": {
            "arch": "ebpf",
            "budget": 1024,
            "image": { "path": "just_tx.bpf.o" }
          }
        }
      },
      "bind": { "session": "ebpf" }
    },
    { "send": { "cmd": { "Run": { "session_id": "$rv32", "until": "Complete" } } } },
    { "send": { "cmd": { "Run": { "session_id": "$ebpf", "until": "Complete" } } } },
    {
      "send": {
        "cmd": {
          "CompareTree": {
            "left": { "Session": { "id": "$rv32" } },
            "right": { "Session": { "id": "$ebpf" } }
          }
        }
      }
    }
  ],
  "assert": [
    { "path": "$last.payload.matchStatus", "eq": "pass" },
    { "path": "$last.payload.summary.fail", "eq": 0 }
  ]
}
```

Interpreter rules: resolve `$bindings` from prior envelopes; `assert` runs on the last envelope unless `path` names `$step[n]`; `expect.kind` maps to exit code + report row.

## Migration steps

1. Add workspace members `classifier-kernel`, `classifier-cli`, `classifier-harness`; extend `rust-ci.sh` crate list.
2. Move `expand`, `engine`, `driver`, `pred_tree`, `pred_match`, image modules into `classifier-kernel` with unchanged Lean calls.
3. Implement `Command`/`Envelope` mapping current HTTP handlers (parity tests: record HTTP responses vs CLI for smoke paths).
4. Shrink `server/src/main.rs` to parse bodies → `Command`, call `kernel.execute`, map `Envelope` to `StatusCode`.
5. Add `classifier-cli` NDJSON loop; wire `scripts/smoke.py` optional `--cli` mode later.
6. Copy four build trees into `tooling/test/xdp/*`; add `base/` and `fail/` cases; implement harness interpreter + JSON report.
7. CI: `classifier-test --workspace tooling` after `rust-ci.sh`; keep `lean-binding/tests` as-is.

## Alternatives considered and rejected

| Alternative | Why rejected |
| --- | --- |
| Rename `server` → lib + thin `main` | Same module boundaries; HTTP and CLI still duplicate request parsing and error paths. |
| `classifier-check` crate for compare/harness only | Expand session stays in server; two domains drift; frontend HTTP still couples to server internals. |
| Harness crate owns `CaseSpec` + shells to CLI | Slower, harder to debug; in-process `Kernel` matches reducer goal and shares pool config. |
| OpenAPI-first code gen | Extra surface; JSON Command enum is smaller and matches existing snapshot JSON. |

## Rationale

A reducer gives **one semantic entry point** for create/step/run/compare while letting adapters differ (REST paths, NDJSON CLI, declarative CaseSpec steps). The harness becomes a **pure command script interpreter** with JSONPath asserts—no text scraping. Session concurrency and Lean pool limits stay inside `Kernel`, so server WS streaming and CLI batch runs behave identically. Smallest public API: four types (`Kernel`, `Command`, `Envelope`, `Arch`) plus harness-only `CaseSpec` types.
