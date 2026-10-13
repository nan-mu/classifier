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

## Claim

`claim: "heuristic"`, `behavioralEquivalence: "notEstablished"`. Not Lean Term equality.
