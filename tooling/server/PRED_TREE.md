# Compare tree

`POST /api/compare/tree` body `{ "left": SnapRun, "right": SnapRun }`.

`SnapRun` accepts a SessionSnapshot shape: `{ arch, nodes[{id,loc,predicates}], edges[{from,to,dir}] }`.

## Domain

The response is a tree of nodes. These are not expand/step State nodes.

Each node has:

- `start`: `create` | `taken` | `not_taken`
- `left` / `right`: ordered list entries for the two architectures
- `matchStatus`: `pass` | `fail`

`pass` means both sides are present, the exit flags are equal, the fork shape is equal, and the ordered observation kinds are equal. Expressions are not read for `matchStatus`. A fork node also has `wire`: `same` or `cross` when only one wiring has that kind order, `undecided` when both wirings do and the branch expressions do not pick exactly one. `undecided` still links children same-direction. `matchStatus` is not behavioral equivalence.

List entries:

- `{ "tag": "start", "kind": "create"|"taken"|"not_taken" }`
- `{ "tag": "pred", "atom": … }` for each local arrival
- `{ "tag": "exit" }` when the path ends at `loc=exit` and the last arrival is not `ret`

Predicate entries are the ordered local arrivals along the segment. For each expand node on the walk, an arrival is a predicate absent from the expand parent. The create root's parent list is empty. A two-arm fork whose straight-walk tail is not `ret` removes the latest `branch` on the walk from the parent list and places that arrival at the start of each child. The expand node that owns both arms may have inherited that branch from the previous step. A walk with no `branch` leaves the parent list as it was built. A non-create child that received no opening moves its first local `branch` to the front. A one-arm edge stays in the same segment. A list whose tail is `ret` has no children. Straight edges stay in the same segment. Order is otherwise walk order. Duplicate arrivals stay. The five normalize kinds are `helper`, `branch`, `ret`, `mapWrite`, and `packetWrite`. Any other kind is kept as an unparsed arrival.

Tree `edges` are only forks. `dir` is `taken` or `not_taken`.

## Phase

`phase` is `local_increment`.

## Claim

`claim` is `crossPred`. `behavioralEquivalence` is `notEstablished`.

A parsed arrival stores CrossPred JSON from `lean_cross_pred_normalize` in `fingerprint`. The server rebuilds one Predicate object from `kind` plus the atom fields and sends an arch CrossEnv.

- `rv32imc` uses `packetBase` `v32:4`, `packetEnd` `add32(v32:4,v32:5)`, and map `1077412584` with `keyBytes` 4 and `valueBytes` 8.
- `ebpf` uses the same `packetBase` and map, with `packetEnd` `add32(v32:4,128)`.
- Any other arch uses `{}`.

A `null` normalize result stores `unparsed:<id>`. Any unparsed arrival fails the node. When every arrival on both sides is normalized, the server sends those JSON texts, in list order, as `{"left":[...],"right":[...]}`. A variable rename can pass when the fingerprint strings differ. The `left` and `right` lists stay on the node for display.
