import { describe, expect, it } from "vitest";
import type { GraphEdge, PredRow, SessionSnapshot } from "./types";
import { branchSource, diffPredicates, formatPred, helperName, processedIds, visibleNodeIds } from "./viewer";

describe("branch source", () => {
  const edges: GraphEdge[] = [
    { from: 1, to: 2, dir: "taken" },
    { from: 1, to: 3, dir: "not_taken" },
    { from: 4, to: 5, dir: "not_taken" },
    { from: 6, to: 7, dir: "only" },
  ];

  it("prefers a branch from the focused node, including NotTaken", () => {
    expect(branchSource(4, edges)).toBe(4);
    expect(branchSource(1, edges)).toBe(1);
  });

  it("falls back to the first graph branch source", () => {
    expect(branchSource(6, edges)).toBe(1);
    expect(branchSource(0, edges.slice(2))).toBe(4);
    expect(branchSource(6, edges.slice(3))).toBeNull();
    expect(branchSource(0, [])).toBeNull();
  });
});

describe("rejected nodes", () => {
  const snap: SessionSnapshot = {
    id: "s", status: "fail", reason: "UndefinedSrc", failed: 2,
    fuel: 5, budget: 10, work: [3], focus: 2, arch: "rv32imc", program: "test.elf",
    insns: [], log: [], cursor_j: 25, proof_note: "",
    nodes: [
      { id: 0, loc: "0", exprs: [], predicates: [], preds: [] },
      { id: 1, loc: "25", exprs: [], predicates: [], preds: [0] },
      { id: 2, loc: "25", exprs: [], predicates: [], preds: [0] },
      { id: 3, loc: "26", exprs: [], predicates: [], preds: [0] },
    ],
    edges: [
      { from: 0, to: 1, dir: "taken" },
      { from: 0, to: 2, dir: "not_taken" },
      { from: 0, to: 3, dir: "only" },
    ],
  };

  it("marks a dequeued rejected leaf as processed, leaving pending work alone", () => {
    expect([...processedIds(snap)]).toEqual([0, 2]);
  });

  it("does not mark an unattempted budget failure as processed", () => {
    const limited = { ...snap, reason: "LimitExceeded", failed: null, work: [2, 3] };
    expect([...processedIds(limited)]).toEqual([0]);
  });

  it("keeps the rejected node visible when same-location arrivals are collapsed", () => {
    const visible = visibleNodeIds(snap, 3, null, true);
    expect(visible.has(2)).toBe(true);
    expect(visible.has(0)).toBe(true);
    expect(visible.has(1)).toBe(false);
  });
});

describe("helper predicates", () => {
  it("formats known and unknown helper ids", () => {
    const lookup: PredRow = {
      kind: "helper",
      event: 166,
      helperId: 1,
      args: ["1077412584", "id32(add32(v32:0,4294967280))"],
    };
    expect(helperName(1)).toBe("lookup");
    expect(formatPred(lookup)).toBe(
      "lookup(0x403802e8, id(add(v0,-16)))",
    );
    expect(formatPred({ kind: "helper", helperId: 999, event: 2, args: [] })).toBe(
      "helper999",
    );
    // Frozen key bytes after ABI arity are omitted from the chip.
    expect(
      formatPred({
        kind: "helper",
        helperId: 1,
        event: 46,
        args: ["1077412584", "id32(add32(v32:0,4294967280))", "a", "b", "c", "d"],
      }),
    ).toBe("lookup(0x403802e8, id(add(v0,-16)))");
  });

  it("diffs helper predicates by event / id / args", () => {
    const a: PredRow[] = [
      { kind: "ret", term: "v32:1" },
    ];
    const b: PredRow[] = [
      ...a,
      { kind: "helper", event: 4, helperId: 5, args: ["5"] },
    ];
    const d = diffPredicates(a, b);
    expect(d.added).toHaveLength(1);
    expect(d.added[0]!.kind).toBe("helper");
    expect(d.removed).toHaveLength(0);
  });
});
