# Compare tree (host, phase 1)

`POST /api/compare/tree` body `{ "left": SnapRun, "right": SnapRun }`.

`SnapRun` accepts a SessionSnapshot shape: `{ arch, nodes[{id,loc,predicates}], edges[{from,to,dir}] }`.

## Domain

The response is a **tree of nodes**. These are not expand/step SemState nodes.

Each node has:

- `start`: `create` | `taken` | `not_taken`
- `left` / `right`: ordered list entries for the two architectures
- optional `tipScore`: soft score on the terminating branch/ret pair

List entries:

- `{ "tag": "start", "kind": "create"|"taken"|"not_taken" }`
- `{ "tag": "pred", "atom": … }` (phase 1: `branch` / `ret` only)
- `{ "tag": "exit" }` when the path ends at `loc=exit` without a `ret`

Tree `edges` are only forks: `dir` is `taken` | `not_taken`.

## Phase

- `phase: "branch_return"` now.
- Later phases append helper / mapWrite / packetWrite into the same lists without renaming nodes.

## Expand-graph note

Branch observations are written onto the `taken` / `not_taken` *child* expand nodes. The tree builder lifts those tip branches into the parent segment so the parent list ends with `branch`, and does not repeat them at the head of the child lists.

## Claim

`claim` is `crossPred`. `behavioralEquivalence` is `notEstablished`.

A phase-1 `branch` or `ret` atom stores CrossPred JSON from `lean_cross_pred_normalize` in `fingerprint` when that call succeeds. The server rebuilds one Predicate object from `kind` plus the atom fields and sends an arch CrossEnv.

- `rv32imc` uses `packetBase` `v32:4`, `packetEnd` `add32(v32:4,v32:5)`, and map `1077412584` with `keyBytes` 4 and `valueBytes` 8.
- `ebpf` uses the same `packetBase` and map, with `packetEnd` `add32(v32:4,128)`.
- Any other arch uses `{}`.

A `null` result keeps the previous soft fingerprint. The atom stays on the list.
