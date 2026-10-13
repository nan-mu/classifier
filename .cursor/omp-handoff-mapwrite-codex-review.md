# Task: Codex review of MapWrite freeze / affineAddress id peel

Spawn `agent: spec-author` for every doc/Lean item below; do not edit them yourself.
Do not edit `tooling/`. Leave commits to the operator. Write a short summary to
`.omp/mapwrite-codex-review-summary.md` when done (dispatcher may write that
summary file after inspecting the spawn’s result).

## Scope (already landed on `agent/lean4-front` in `49a7776`)

Prior “review” ran on DeepSeek because Codex was disabled and the brief wrongly
asserted a `spec-author` identity. This pass must use the real `spec-author`
spawn (`openai-codex/gpt-6.1-sol:high`).

### Review / fix if needed

1. `RV32IMC/Expr.lean` — `affineAddress` peels `.id` (mirror `lookupAddress`);
   related `#guard`s including freeze via `readStackBytes` on
   `id32(add32(sp,-16))`.
2. `doc/Expr/Term/solve.md` and `doc/Predicate/MapWrite谓词.md` — id-peel
   invariant wording vs actual Lean behavior.
3. Soundness: peel belongs in recognizers not `solve_w`; dual SW MapWrite for
   u64 `*value += 1` remains a tooling observation, not a Lean proof.

### Tooling-side facts (Cursor; read-only for omp)

- Fixture: `tooling/fixtures/just_tx.elf` — map `0x403802e8`, key 4, value 8.
- C: `libbpf-mcu/tests/xdp/just_tx.c` — lookup `&rxcnt` then `*value += 1`.
- Measured after peel + Meta.maps: budget 512 → nodes 549 / mapWrite present;
  budget 1024 → complete, fuel 187, nodes 882. `cargo test -p server just_tx`
  2 passed under Cursor.

### Gates for the spawn

- `lake build ClassifierExpr PathMerge RV32IMC EBPF`
- Doc gates under `.audit/` if docs change
- Confirm in the summary which **provider/model** the spawn actually used
