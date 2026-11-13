# Audit: alive2-rocq

Task book: `/tmp/pr6-handoff/pr6_alive2_rocq/PR6_TASK.md` (attachment `pr6_alive2_rocq_handoff.zip`, no later revision). Fixtures: `/tmp/pr6-handoff/pr6_alive2_rocq/fixtures.json`.
PStack: `/Volumes/SSD/.claude/plugins/cache/cursor-plugins/pstack/0.15.36` v0.15.36, playbook `feature`.
Base: `agent/alive2-ebpf` (`1dbfbcdb65ed687624c6d36f4b33843ae42fd3b6`, PR #5). Branch: `agent/alive2-rocq`. PR: https://github.com/nan-mu/classifier/pull/6
Worktree: `/Volumes/SSD/bs/classifier-alive2-rocq`.

This file is the committed requirement checklist. The decision trail is `.audit/alive2-rocq.tsv`, which `.gitignore` already ignores. The dirty files on the main checkout belong to another task and stay untouched. PR #5's symbolic matrix is not acceptance evidence for this task.

Upstream pin: `https://github.com/OpenSourceVerif/linux-ebpf-semantics` commit `78d65a77592aae84b31f86385f8be4ab83b45ccb`, copied under `alive2/rocq/upstream/` and recorded in `alive2/rocq/PIN`. The build runs that tree's own `make` with Coq 8.19.0 and CompCert 3.15 on opam switch `linux-ebpf`. The selected switch `sf` is Rocq 9.2 and is not used.

## Exit criteria

1. Unmodified upstream `make` builds at the pinned SHA, or the checklist records the exact toolchain blocker. No replacement semantics.
2. Five normal inputs produce step-aligned equal traces from the Rocq oracle and from concrete execution of the real lifter's IR.
3. The DIV64 zero-guard mutation fails the comparator at the first relevant divergence, and the lifter is restored before commit.
4. Every row below is `yes` with evidence, or stays `no` with the reason in Open issue.

| # | Requirement (from task book) | Implemented | Verified | Evidence | Open issue |
|---|------------------------------|-------------|----------|----------|------------|
| 1 | New branch `agent/alive2-rocq` from existing `agent/alive2-ebpf`. Do not merge into `main`. | yes | yes | https://github.com/nan-mu/classifier/pull/6 base `agent/alive2-ebpf` | — |
| 2 | Check concrete per-eBPF-instruction state changes of the actual PR #5 lifter against the existing Rocq reference. | yes | yes | `./alive2/build/ebpf-concrete --out /tmp/ebpf-concrete-vendored` exit 0, six rows | — |
| 3 | No SMT, symbolic execution, theorem proving, ISA reimplementation, broad fuzzing, or rewrite of PR #5. | yes | yes | `alive2/CMakeLists.txt` target `ebpf-concrete` links `ebpf_decode.cpp`, `ebpf_lift.cpp`, `ebpf_concrete.cpp` only | — |
| 4 | On a mismatch, fix the adapter or lifter before claiming PASS. Do not accept a vacuous comparator. | yes | yes | negative row prints `pc 1 status alive2=UB rocq=NEXT` | — |
| 5 | Pin `linux-ebpf-semantics` at one recorded commit SHA. Keep upstream `theories` unmodified. Adapters live separately. | yes | yes | `alive2/rocq/PIN`; `alive2/rocq/rocq_step.ml` is outside `upstream/` | — |
| 6 | Reuse upstream `code := list int64`, `find_instr`, register/memory/outcome, and `exec_instr` / `step`. Do not port `eval_alu64`, `decode_insn`, or `exec_instr` into Rust. | yes | yes | `alive2/rocq/rocq_step.ml` calls extracted `find_instr` and `exec_instr` | — |
| 7 | `Validation.v` / `Extraction.v` are integration examples only. Their `semantics_validation` does not export the required reference traces. | yes | yes | driver prints its own steps; `semantics_validation` is not called | — |
| 8 | A small Rocq wrapper extracts a concrete step runner to OCaml. Upstream toolchain is Coq 8.19 + CompCert. Explicit input registers and finite fuel. Fuel exhaustion is `INCOMPLETE`, never PASS. Original `Stuck` is preserved. | yes | yes | vendored `make` during `cmake --build alive2/build --target ebpf-concrete`; `printf 'bytes 0500ffff00000000\n' \| ./alive2/build/rocq/rocq-step` ends `status INCOMPLETE` | — |
| 9 | Document a controlled common initial-state relation. Do not equate `Vundef` with zero. Seed the explicitly relevant integer registers. R10 stays a pointer outside the observable subset. Reject programs that read R10. | yes | yes | `alive2/rocq/README.md`; trace key `exclusions`; `rocq_step.ml` rejects an input register outside r0–r9 | programs that read r10 are rejected at the input list, not by executing a load of r10 |
| 10 | Preserve status, PC, and absence of memory side effects. Do not claim whole-machine equivalence from a return value alone. | yes | yes | traces for `jgt64-11` and `jgt64-10` differ in pc sequence, not only in r0 | — |
| 11 | Run the real PR #5 lifter on the same bytes, then concretely evaluate the generated Alive2 IR. Do not call `ebpf_ref.cpp`, do not reuse the upstream eBPF decoder for the Alive2 path, do not execute the machine code a second time, and do not use `util::sym_exec` as the concrete executor. | yes | yes | `alive2_trace` in `alive2/src/ebpf_lift.cpp`; CMake pre-build grep forbids `sym_exec`, `ebpf_run.h`, and `ebpf_ref` | — |
| 12 | The concrete IR evaluator supports only the constructs these three programs emit: 64-bit bitvectors, SSA, phi with a chosen predecessor, add/sub, icmp, br, ret, udiv/sdiv, and the conversions or guards actually encountered. Unsupported IR, poison, or UB is a named non-PASS status. | yes | yes | five ordinary rows PASS; mutation row status `UB` | — |
| 13 | A sidecar from the actual lifter names each original pc and the SSA register values when that machine instruction completes, including multi-block branches. Compare at eBPF instruction boundaries, not IR lines. Traces come from execution, not from `expected_r0`. | yes | yes | `SourceEnd` in `ebpf_lift.cpp`; `jgt64-11` steps are pcs 0, 1, 4, 5 | — |
| 14 | Emit `rocq.trace.json` and `alive2.trace.json` with bytes/hash, the shared concrete input, ordered pcs, source bytes, status (`NEXT`, `EXIT`, `STUCK`, `UB`, `INCOMPLETE`, `UNSUPPORTED`), before/after observable registers (`BV64`, `UNDEF`, `PTR`), PC, return value, empty memory summary for these ALU programs, and the explicit exclusion rules. | yes | yes | `/tmp/ebpf-concrete-vendored/div64-7-2/rocq.trace.json` and `alive2.trace.json` | — |
| 15 | The comparator checks PC sequence, step status, and every defined comparable register after each eBPF instruction. It rejects a missing step, UB vs defined, a truncated trace, an unsupported value, and an unexpected memory effect. A mismatch prints one first divergence and writes full traces only to files. | yes | yes | `first_divergence` in `ebpf_concrete.cpp`; stdout is one `FAIL` line plus `suite=PASS` | — |
| 16 | DIV64 `r1=7,r2=2` gives `r0=3`, with the Rocq run as the oracle and concrete IR execution as the target. `expected_r0` is only a sanity check. | yes | yes | row `div64-7-2 comparator=PASS sanity=ok`; both traces r0 `0000000000000003` at pc 1 | — |
| 17 | DIV64 `r1=7,r2=0` gives `r0=0`. Same oracle rule as row 16. | yes | yes | row `div64-7-0 comparator=PASS sanity=ok`; both traces r0 `0000000000000000` at pc 1 | — |
| 18 | SDIV64 `r1=INT64_MIN,r2=-1` gives `r0=INT64_MIN`. | yes | yes | row `sdiv64-min--1 comparator=PASS sanity=ok`; r0 `8000000000000000` | — |
| 19 | JGT64 `r1=11` gives `r0=12`. | yes | yes | row `jgt64-11 comparator=PASS sanity=ok`; taken pcs 0, 1, 4, 5; r0 `000000000000000c` | — |
| 20 | JGT64 `r1=10` gives `r0=9` on the other CFG path. | yes | yes | row `jgt64-10 comparator=PASS sanity=ok`; fall-through pcs 0, 1, 2, 3, 5; r0 `0000000000000009` | — |
| 21 | Negative test bypasses the lifter DIV64 zero-divisor guard. The comparator must fail at the first relevant divergence for `7/0`. Restore the lifter before committing. | yes | yes | row `div64-7-0-div-zero-as-ub` prints `pc 1 status alive2=UB rocq=NEXT`; the flag is `LiftBug::DivZeroAsUb` on that row only (`ebpf_lift.cpp` still has the guard) | — |
| 22 | Do not count the PR #5 symbolic matrix as this task's acceptance. No random fuzzing and no large case dump. Deliver a 6-row result table and one positive and one negative trace sample. | yes | yes | stdout is six rows; samples `/tmp/ebpf-concrete-vendored/div64-7-2/` and `div64-7-0-div-zero-as-ub/` | — |
| 23 | Reproduction command, upstream SHA, trace format, limitations, and this evidence table are in the PR. Open the PR into `agent/alive2-ebpf` only when the checks work. Otherwise leave a Draft that states the blocker. Do not merge. | yes | yes | https://github.com/nan-mu/classifier/pull/6 and `alive2/rocq/README.md` | — |
| 24 | The result is bounded concrete translation validation for these inputs, not a proof of all inputs or all ISA instructions. | yes | yes | `alive2/rocq/README.md` states the limit | — |
