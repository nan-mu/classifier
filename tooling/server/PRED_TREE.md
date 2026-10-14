# Compare tree

`POST /api/compare/tree` body `{ "left": SnapRun, "right": SnapRun }`.

`SnapRun` accepts a SessionSnapshot shape: `{ arch, nodes[{id,loc,predicates}], edges[{from,to,dir}] }`.

## Domain

The response is a tree of nodes. These are not expand/step SemState nodes.

Each node has:

- `start`: `create` | `taken` | `not_taken`
- `left` / `right`: ordered list entries for the two architectures
- `matchStatus`: `pass` | `fail`

`pass` means both sides are present, the exit flags are equal, and the LCS of normalize keys has no `onlyLeft` or `onlyRight` slot. Every other case is `fail`, including a one-sided arm, an exit mismatch, and an extra predicate. `matchStatus` is not behavioral equivalence.

List entries:

- `{ "tag": "start", "kind": "create"|"taken"|"not_taken" }`
- `{ "tag": "pred", "atom": … }` for each local arrival
- `{ "tag": "exit" }` when the path ends at `loc=exit` and the last arrival is not `ret`

Predicate entries are the ordered local arrivals along the segment. For each expand node on the walk, an arrival is a predicate absent from the expand parent, using a `predKey`-style identity. The create root's parent list is empty. A `taken` or `not_taken` head's parent is the fork node. A branch written on a successor stays on that successor's segment. Order is walk order. Duplicate arrivals stay. The five normalize kinds are `helper`, `branch`, `ret`, `mapWrite`, and `packetWrite`. Any other kind is kept as an unparsed arrival.

Tree `edges` are only forks. `dir` is `taken` or `not_taken`.

## Phase

`phase` is `local_increment`.

## Claim

`claim` is `crossPred`. `behavioralEquivalence` is `notEstablished`.

A parsed arrival stores CrossPred JSON from `lean_cross_pred_normalize` in `fingerprint`. The server rebuilds one Predicate object from `kind` plus the atom fields and sends an arch CrossEnv.

- `rv32imc` uses `packetBase` `v32:4`, `packetEnd` `add32(v32:4,v32:5)`, and map `1077412584` with `keyBytes` 4 and `valueBytes` 8.
- `ebpf` uses the same `packetBase` and map, with `packetEnd` `add32(v32:4,128)`.
- Any other arch uses `{}`.

A `null` result stores `unparsed:<id>`. That key matches nothing, including another null result. Equality uses the normalize JSON only. LCS keys are those JSON strings. On equal DP scores the backtrack prefers `onlyRight`.
