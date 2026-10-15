# Decision trail: just_tx compare-tree fail→0

Exit predicate: dual just_tx budget 1024, every compare node `matchStatus=pass`.

| iter | change | measured | keep? |
|------|--------|----------|-------|
| 0 | baseline after F1 carrier erase | pass 34 / fail 67 | n/a |
| 1 | host polarity swap on dual taken tips + write-run offset sort | pass 46 / fail 43; onesided 0 (was 24) | keep |
| 1b | unify rewrite branch dir to compare-tree edge | still 46/43 (N15 still CP-Add/End/key) | keep (correct) |
| 2 | omp MapWrite eBPF generation | eBPF emits 165 mapWrites; asym still 15 (2 vs 1 width) | keep |
| 3 | omp split 8-byte MapWrite → two ×4 | mapWrite_asym 15→0; still pass 46 / fail 43 | keep |
| 4 | omp CP R1–R4 (add commute, zero-id, end, sext peel) | Lean landed | keep |
| 5 | host per-obs storeBytes (pw=2, mw=4) | pass 70 / fail 19 (was 46/43) | keep |
| 6 | host VLAN OR commute attempt | regressed 70/19 → 30/61; reverted | discard |
| 7 | omp MapWrite carry R5/R6 | pass 85 / fail 4 (only VLAN 3,4,7,8) | keep |
| 8 | omp VLAN fixture reorder | rejected (compiled immediates; no Lean knob) | discard |
| 9 | host VLAN OR-arm matchStatus (TPID pair, same field+rel) | pass 89 / fail 0 | keep |

Principles applied (leaf read this session): Never Block on the Human (keep going), Fix Root Causes (one_sided from polarity, not Rempty paint), Model the Domain (dual_rel + tip peek), Laziness Protocol (smallest host fix before more Lean).
