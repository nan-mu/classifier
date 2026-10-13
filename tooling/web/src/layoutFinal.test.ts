import { describe, expect, it } from "vitest";
import { layoutFinal } from "./layoutFinal";
import { measureLayout } from "./layoutMetrics";
import type { GraphEdge, GraphNode } from "./types";

const node = (id: number): GraphNode => ({
  id,
  loc: String(id),
  exprs: [],
  predicates: [],
  preds: [],
});

const e = (
  from: number,
  to: number,
  dir: GraphEdge["dir"] = "only",
): GraphEdge => ({ from, to, dir });

describe("layoutFinal", () => {
  it("lays out a small DAG with no crossings", () => {
    const nodes = [0, 1, 2, 3, 4, 5, 6].map(node);
    const edges = [
      e(0, 1, "taken"),
      e(0, 2, "not_taken"),
      e(1, 3),
      e(2, 4),
      e(3, 5, "taken"),
      e(3, 6, "not_taken"),
    ];
    const pos = layoutFinal(nodes, edges);
    const m = measureLayout(pos, edges);
    expect(Object.keys(pos).length).toBe(7);
    expect(m.crossings).toBe(0);
    expect(m.overlaps).toBe(0);
    expect(m.stacks).toBe(0);
  });

  it("keeps card clearance with tight final gaps", () => {
    const nodes = [0, 1, 2].map(node);
    const edges = [e(0, 1, "taken"), e(0, 2, "not_taken")];
    const pos = layoutFinal(nodes, edges);
    const dy = Math.abs(pos["1"]!.y - pos["2"]!.y);
    // centers at least NODE_H apart (no overlap); sep is border gap, not pitch
    expect(dy).toBeGreaterThanOrEqual(72 - 1e-6);
    expect(pos["1"]!.x).toBeCloseTo(pos["2"]!.x, 5);
  });
});
