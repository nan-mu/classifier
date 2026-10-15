# Synthesis: domain + JSON CLI + CaseSpec suite

## Base

[Candidate B](arena-test-cli-candidate-b.md) (command reducer / shared `execute`).

[Candidate A](arena-test-cli-candidate-a.md) arrived after the N−1 pick. Kept as
graft source, not a base swap.

## Cross-judge

| Criterion | A | B | Winner |
| --- | --- | --- | --- |
| Public surface | Session open/run + compare_tree | Kernel/Command/Envelope | B (one entry) |
| CaseSpec clarity | `op` + `artifacts` + expect.kind | Nested Command send | A graft |
| CLI contract lock | Harness spawns CLI | In-process harness | B (faster CI); CLI still JSON |
| Migration risk | 3 new crates + session files | 4 crates or flat lib | Laziness flat |
| Fail without HTTP | Yes via CLI | Yes in-process | Tie |

**Base remains B.** Packaging stays one `server` crate (lib + HTTP + `classifier` bin).

## Grafts from A

1. **CaseSpec shape.** Prefer A’s `artifacts` / `steps[].op` / `bind` over B’s
   nested `send.cmd`. Interpreter maps ops → `Command` internally.
2. **`expect.kind`.** `pass` | `fail` | `error`.
   - `pass`: assertions hold; session/compare success as specified.
   - `fail`: intentional session `status:fail` or compare `fail_at_least`.
   - `error`: decisive step returns `ok:false`.
3. **Exit codes.** 0 = `ok:true` (or all cases pass); 1 = domain error; 2 = usage.
4. **`map_elf`.** eBPF create may take companion ELF bytes for map rows (default
   remains just_tx product maps when omitted).
5. **Rejected from A.** Process-spawn harness (slower; does not earn its place
   while CLI still emits the same Envelope). Separate `domain`/`cli`/`harness`
   crates (same API, more Cargo surface).

## Locked packaging

```text
tooling/server/
  src/lib.rs              # Kernel + Command + Envelope + modules + harness
  src/main.rs             # axum adapter
  src/bin/classifier.rs   # JSON CLI + `test` subcommand
tooling/test/{base,xdp,fail}/
```

## Locked API

- `Kernel::execute(Command) -> Envelope`
- CLI prints one Envelope JSON; subcommands or `exec` stdin OK
- Harness in-process; CaseSpec uses A’s op/artifacts/expect vocabulary
- Suites: `base`, `xdp` (four pairs under `tooling/test/xdp/`), `fail`

## Verification gates

1. `cargo build -p server` (lib + bins)
2. `classifier` create+run just_tx → JSON `ok:true`
3. `classifier test --root tooling/test` green
4. HTTP smoke create default still works