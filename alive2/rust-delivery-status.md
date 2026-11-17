# Rust file compiler delivery status

This branch is a Draft prototype. The 17 snapshotted raw BPF objects convert to standalone Alive2 text and load in a separate C++ process. Semantic preservation by the Rust implementation is unproven.

## Recorded checks

| Check | Result | Evidence |
| --- | --- | --- |
| Rust compiler and CLI tests | 26 passed | `cargo test --manifest-path tooling/Cargo.toml -p ebpf-to-alive2 --offline` |
| Rust formatting and workspace clippy | passed | `tooling/scripts/rust-ci.sh`, with the installed Lean toolchain on PATH |
| Explicit legacy profile tests | 2 passed | `cargo test --manifest-path tooling/Cargo.toml -p server --lib profile::tests --offline` |
| Loader validation self-test | passed | `alive2/build/alive2-load --self-test` |
| Real corpus compile and independent load | 17 of 17 | `corpus/rust-file-verification.json` |
| Pinned parser/printer self-consistency, including instruction text | 17 of 17 | same report; compares kinds, types (including declaration arguments), operands, targets, predicates, phi labels, memory effects, and alignment; not an independent semantic oracle |
| IR loading independent of origin metadata | 17 of 17 | same report; missing and corrupt origin are never read by the loader; origin validation is not implemented |
| Upstream symbolic executor smoke | div2, xdp_drop, and helper_loop with unroll 1 completed | same report; loop without a bound rejected; no equivalence or safety solver result |

The integration command is in `alive-file-v1.md` and implemented in `tests/run-rust-file-e2e.py`. The recorded report binds the compiler and loader binaries, input snapshot, and per-program input/output files by SHA-256. Those binary hashes are machine/build-specific. Rebuild and rerun to obtain a new report.

Generated `.alive`, origin, per-program conversion reports, and normalized files are outside the input publisher tree at `/Volumes/SSD/bs/classifier-output/alive2-rust-compiler`. The committed verification report is an index into that directory. The input snapshot contains its own copied raw BPF fixtures and hashes.

The server profile test initially failed to link because this worktree had no Lean shared libraries. Building `Core:shared`, `Node:shared`, `RV32:shared`, and `EBPF:shared` resolved that prerequisite; the server profile tests then passed. The full server test suite and legacy profile runtime outcomes were not rerun for this change.

## Changes in this pickup

The interrupted register-facts migration now compiles. Scalar values cannot silently become packet pointers. Packet addresses, context, stack, map handles, and map values retain distinct facts; typed stack spills track their offsets and reject incompatible partial reloads. ALU32 moves and pointer differences in the actual corpus are handled explicitly. Expanded division blocks provide their actual outgoing predecessor labels to phi nodes.

The loader validates pins, syntax, references, types, terminators, reachability, SSA dominance, phi predecessor sets, call signatures, and memory effects. Printer round trips exposed two real protocol gaps: bare declaration/call names, and missing call memory attributes. Calls now inherit declared effects and reject contradictory explicit effects. Neither the upstream executor nor its unroller was modified.

ELF loading validates complete table entries and relocation targets. It rejects multiple functions in a selected section and functions that do not span that section, rather than silently compiling a different byte range. CLI output publication checks input hashes, uses staged files and a report-last completion marker, and invalidates old outputs on caught conversion failures. A corpus ownership file tracks output names: subsequent invocations invalidate managed reports before manifest parsing and remove managed artifacts for programs omitted from a valid manifest. Unrelated files are preserved. Origin names are actual emitted definitions, including block-entry phis and separate prologue definitions; branches and full LDDW instruction bytes are retained.

The DeepSeek audit found six actionable issues: invalid signed 64-bit loads, invalid sign-ext stores, omitted phi origin names, stale batch reports, misplaced headers, and sanitized map-name collisions. All have fixes and regressions. The decoder accepts sign-ext memory mode only for narrow loads. Origin coverage is checked in both directions. Loader headers must precede the body, and distinct map symbols cannot collapse to one parameter. Declaration input types and a real loop smoke now extend the recorded checks. The audit inspected only the resumed activity slice, not the entire historical thread.

## Remaining obligations

1. **Implementation proof:** no mechanized connection from the actual Rust decoder/lifter and produced text to the pinned Rocq ISA and Alive2 semantics exists. The required arbitrary-state simulation, events, UB/poison, memory, helper contracts, and loop relation remain open. The earlier C++ exhibit and Rocq checks do not discharge this obligation. No upstream semantics, axioms, or admitted lemmas were added in this pickup.
2. **Artifact proof and semantic corruption checks:** there is no independent per-artifact semantic certificate checker. Parser rejection tests cover malformed structure. They do not prove rejection of a well-typed, semantically corrupted ADD, division guard, jump, phi, store, or helper call. Reports retain separate `model_proof`, `artifact_proof`, and `implementation_proof` fields with `not_proven`.
3. **Full source-state origin:** instruction-to-SSA metadata does not yet provide checkpoint expressions for every R0–R10/RAX/PC/stack/code-id/tail-call state component. `state_mapping = "incomplete"` and `source_view = "incomplete"` make that boundary explicit. There is no source-view consumer or source-state relation checker.
4. **Task A contract and consumers:** the authoritative A-task `index.toml` is absent. `corpus/snapshot.toml` is the observed 17-file fallback, not a replacement claim for that contract. `profile.toml` now explicitly selects `legacy-dual-arch`; the server rejects raw BPF results under that interpretation. Migration of the old page to the eventual raw BPF manifest/report format and corresponding legacy fixture provenance remains open.
5. **General ELF and state coverage:** the compiler supports one function spanning its executable section, little-endian ELF64 ET_REL BPF, and its documented instruction/provenance subset. Other valid BPF programs may be rejected. Snapshot success does not establish general completeness.

These gaps prevent promotion from Draft. The user-authorized fallback is a runnable, reviewable prototype with its proof boundary recorded; it is not full completion of the original formal compiler contract.
