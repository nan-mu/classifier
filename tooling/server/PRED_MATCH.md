# Host fuzzy Predicate match

`POST /api/compare/predicates` with body `{ "left": PredRun, "right": PredRun }`.

`PredRun` is `{ arch, nodes: [{ id, loc, predicates }] }`. Extra snapshot fields are ignored.

## Response contract (stable for a later Lean port)

- `status`: `"matched"`
- `claim`: `"heuristic"` until Lean Term equality exists
- `behavioralEquivalence`: `"notEstablished"`
- `note`: human-readable disclaimer
- `locations[]`: per-`loc` buckets with `pairs[]`
- pair `status`: `"matched" | "onlyLeft" | "onlyRight"`
- matched pairs carry `score: { kind, fields, terms, overall }` in `[0,1]`

## Heuristic (Rust `pred_match.rs`)

1. Kind gate after alias normalize (`return`→`ret`, `map_write`→`mapWrite`, …). Different kinds never match.
2. Field-key overlap (ignore `event` identity).
3. Soft term compare: peel `zext` / `extract` / `sext` wrappers, token Jaccard + Levenshtein ratio on selected fields per kind.
4. Greedy bipartite match per `loc` with floor `overall >= 0.35`.

This is intentionally fuzzy. Do not treat scores as soundness evidence. Lean should keep the same JSON tags when it replaces the scorer.
