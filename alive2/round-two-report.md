# Round-two compiler report

## Actual compiler result

PR7 round-two A1–A12 fixes retain the Rust ELF reader, decoder, register-facts analysis, and text emitter. Emission spans produce one authoritative generated-instruction ledger; the legacy origin SSA arrays derive from that ledger. No new general IR AST or source-state type system was introduced.

| Request | Delivered behavior |
| --- | --- |
| A1–A2 | Compiler formatting in local tooling and Actions; compiler tests and alive2 path triggers added; existing denial lints retained. Local checks pass. Remote Actions results must be checked separately after pushing. |
| A3 | Function/declaration/call memory attributes checked through Alive2 APIs; unknown attribute tokens rejected. |
| A4 | Direct phi object checks for i1/i8/i16/i32/i64 signed and unsigned boundary literals, values, types, and predecessor names, including the upper half of u64. |
| A5 | Exact v1/pin headers, missing/wrong/substrings/duplicate negatives. |
| A6 | Seven independent compiler→text→loader fixtures: arithmetic, condition, forward jump, phi, i32 division, helper/memory attributes, and loop phi. Fixed expected types, opcodes, operand aliases, targets, phi pairs, attributes, and loop-phi source slots are compared with API-derived inspect fields. |
| A7 | Helper 1 requires a dereferenceable key, preserves MapVal result facts, and clobbers r1–r5. Context/packet moves, typed spills, ALU32/MOVSX, mixed scalar/pointer operations, conflicting phis, and uninitialized reads have regressions. Errors include source context where known. |
| A8 | Origin revision 2 adds decoded instructions, all generated instructions (including void/store/branch/return and division expansion), source/generated CFG, and phi inputs with generated predecessors and reaching source definitions. MOV-without-IR rows and full LDDW bytes remain. Production and independent gate checks validate coverage and references. |
| A9–A10 | All 17 fixtures have explicit expected status, entry, section, decoded count, and exact independently decoded backedges. Typed outcomes are converted/unsupported/invalid_elf/invalid_instruction/internal_error; unexpected emission and I/O remain internal errors. Failures remove success products and publish separate categorized failure JSON when writable. |
| A11–A12 | Resolved paths and existing ancestors protect input/source aliases before mutation. Missing source-root discovery requires an explicit root; that root cannot exempt a discovered checkout. Staging uses exclusive file creation, reports publish last, ownership cleanup preserves unrelated files, and failed verification reruns remove stale success evidence. |

The structure fixtures contain fixed expected instruction models separate from compiler output and normalized text. Parser/printer round trips remain useful additional checks, but are not the independent oracle. The corpus origin checker verifies emitted instruction coverage, unique IDs and SSA definitions/references, source byte coverage, owners, generated edges, and phi predecessor/source references. A dedicated division/phi regression checks the actual generated predecessor after expansion.

## Recorded local checks

All commands below completed successfully in the retained checkout. Generated artifacts use an external temporary directory; no source-tree outputs were published.

```sh
cargo +nightly test --manifest-path tooling/Cargo.toml -p ebpf-to-alive2 --quiet
tooling/scripts/rust-ci.sh
cmake --build alive2/build --target alive2-load -j 4
alive2/build/alive2-load --self-test
cargo +nightly build --manifest-path tooling/Cargo.toml -p ebpf-to-alive2 --quiet
run_dir=$(mktemp -d "${TMPDIR:-/tmp}/alive2-round-two.XXXXXX")
python3 alive2/tests/run-rust-file-e2e.py \
  --compiler "$PWD/tooling/target/debug/ebpf-to-alive2" \
  --loader "$PWD/alive2/build/alive2-load" \
  --index "$PWD/alive2/corpus/snapshot.toml" --out-dir "$run_dir"
python3 alive2/tests/evidence-publication.py \
  --compiler "$PWD/tooling/target/debug/ebpf-to-alive2" \
  --loader "$PWD/alive2/build/alive2-load" \
  --index "$PWD/alive2/corpus/snapshot.toml"
git diff --check
```

Results: **37 Rust tests passed** (1 publication unit, 11 CLI, 4 lift, 5 typed-outcome, 9 provenance, 7 ELF/section); nightly fmt and workspace clippy passed with denial lints; the rebuilt loader self-test passed. The integration gate passed **7 independent structural fixtures, 17 conversions/loads/normalization round trips, and 3 symbolic-execution smokes**. `helper_loop` requires an explicit unroll bound; rejection without a bound is also checked. The separate evidence publication suite passed **3 failed-rerun cases** (compiler failure, loader failure, and normalization publication failure), preserving unrelated files. The Rust publication test induces final-report rename failure and checks cleanup.

The external `verification.json` records compiler/loader/snapshot hashes and per-program ELF/Alive/origin hashes. It is published only after all checks succeed. The committed `corpus/rust-file-verification.json` is the refreshed index for this round; its artifact paths are relative to the external output directory. Original source/object paths are historical provenance, not runtime path assumptions. Rebuild and rerun to produce independent evidence. Remote CI results remain separate from local validation.

An independent Tester and a Qwen4 Reviewer reproduced the local checks and matched per-program artifact hashes. The reviewer independently checked 436 phi inputs across all 17 programs with zero reaching-definition mismatches. The parent then added the seventh fixture, a loop phi with exact incoming source slots, and reran the structural and integration gates. The reviewer could inspect the current audit rows and files but could not access the complete parent transcript.

## Fixed snapshot outcomes

Backedges are source instruction slot pairs `(from, to)` decoded independently from the ELF. Counts exclude LDDW continuation slots. All actual statuses matched the explicit expected `converted` status; reason `—` means no rejection.

| Program | ELF SHA-256 | Entry | Section | Count | Expected / actual | Backedges | Reason |
| --- | --- | --- | --- | ---: | --- | --- | --- |
| bitswap | `775dc8cf4a221765493bf915d79d54905e5f456c013943718d9237e20582a980` | bitswap | xdp | 68 | converted / converted | `[[61, 24]]` | — |
| bsort | `9c477f4bf4cddbf47748c5e7c2154b9f9cd967e57bb09b44d6aaa7e8c63daf18` | bsort | xdp | 619 | converted / converted | `[]` | — |
| buf | `9850410ce7b7fbef0174791ecfe621d485909c193294cf5ffab180d5c45c899c` | buf | xdp | 46 | converted / converted | `[[29, 21]]` | — |
| case_mark | `2d440d2e2f9370670073b5ffe50fc704732e326a76da4b4f99506af44c52649e` | xdp_prog1 | xdp1 | 104 | converted / converted | `[]` | — |
| case_swap | `2c93af665233795f5a7df5db2d301736469ef71e6a7cc355a27c96e7702c87b2` | xdp_prog1 | xdp1 | 104 | converted / converted | `[]` | — |
| div2 | `1d590716c4a7f4e3c583280c4a985ddfaa193e758e6c7037c2c36a17df2395a4` | div2 | xdp | 29 | converted / converted | `[]` | — |
| fib | `598dbebb210b224b1c8ef5cdbd4245fd5bebfaafc8ca8e0ab29eb4ef601d825c` | fib | xdp | 41 | converted / converted | `[[29, 25]]` | — |
| firewall | `143bd90de464fd13d032818d5a9f626044238c44a34230319d93b36161a9aa3f` | firewall | xdp | 22 | converted / converted | `[]` | — |
| fletcher32 | `80ee54d740ac5df55b3ef80d7ee3ac095f92fb95294861dfd2bec920081d9b26` | fletcher32 | xdp | 402 | converted / converted | `[[401, 395]]` | — |
| helper_loop | `973a78d63dba1f7ab4b1d2246855f0c92b17d1f0d5d4372dc52308622872dcb9` | helper_loop | xdp | 27 | converted / converted | `[[23, 13], [27, 13]]` | — |
| incr | `8103639ae59dff73ffe7eef0c43cd9e7c3893bcc4a570bfad674635b66eca99b` | incr | xdp | 30 | converted / converted | `[]` | — |
| just_drop | `78090f2b29c64caea9ff52f2ede01ab27f3b69e4c46be41030105760f7c9ed24` | xdp_prog1 | xdp1 | 33 | converted / converted | `[]` | — |
| just_tx | `97d6033cd68d1d56b193dd303ce04a2ffcc1c607402ebb8fc7faa15f41317201` | xdp_prog1 | xdp1 | 57 | converted / converted | `[]` | — |
| memcpy | `d6c2f0cce069229f473fb49983147e7ca351a9effad43c3ddda395b62f46a1fa` | memcpy_xdp | xdp | 73 | converted / converted | `[]` | — |
| merge_try | `19432b3394729eb9dd1698f317ba31223d1afe749da03dad0bf14be1a09d88ba` | merge_try | xdp | 16 | converted / converted | `[]` | — |
| square | `d99e28628825f172ea6815a58b0bb5e77567b1468a49f0997686ada5123a90d1` | square | xdp | 30 | converted / converted | `[]` | — |
| xdp_drop | `1197f07a580c3cd1b971e0de6ff2edfabcc1af78830b7f198d8d4dee09b76184` | xdp_firewall | xdp | 21 | converted / converted | `[]` | — |

## Known limitations

Machine-code and Rocq state-transition proofs are explicitly outside this round. `model_proof`, `artifact_proof`, and `implementation_proof` remain `not_proven`; no semantic equivalence, general algorithm verification, or independent artifact certificate is claimed. Symbolic-execution smoke completion does not discharge these proofs.

Full register/PC/stack checkpoint state relations and a source-view consumer remain incomplete. Phi source slots identify reaching register definitions, not complete symbolic source states. Helper 1 retains its documented external memory-effects contract; these tests do not prove helper semantics or map safety. The snapshot remains a 17-object fallback because Task A's authoritative index is absent. General ELF/multiple-function support remains limited to the documented subset. Publication uses report-last completion markers, not a crash-safe multi-file transaction; concurrent writers to the same destinations remain unsupported.

[Pre-implementation analysis](../analysis/README.md) is historical. [Delivery status](rust-delivery-status.md) labels prior-run evidence separately. The implementation stage made no commits, pushes, or PR changes. The parent owns independent testing, review, and delivery to the existing PR.
