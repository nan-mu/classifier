import { describe, expect, it } from "vitest";
import { splitExprs } from "./exprs";
import type { ExprRow, GraphNode } from "./types";

const binding = (reg: string, term: string): ExprRow => ({ reg, rel: "eq", term });
const node = (id: number, exprs: ExprRow[], preds: number[] = []): GraphNode => ({
  id, loc: String(id), exprs, predicates: [], preds,
});

describe("successor expression deltas", () => {
  it("shows both branch deltas with their own target and direction", () => {
    const unchanged = binding("real32:1", "18446744073709551615");
    const root = node(0, [binding("real32:10", "0"), unchanged]);
    const taken = node(1, [binding("real32:10", "1"), unchanged], [0]);
    const notTaken = node(2, [binding("real32:10", "2"), unchanged], [0]);
    const split = splitExprs(root, [root, notTaken, taken], [
      { from: 0, to: 1, dir: "taken" },
      { from: 0, to: 2, dir: "not_taken" },
    ]);
    expect(split.eg).toEqual(root.exprs);
    expect(split.eiOut).toEqual([
      { to: 2, dir: "not_taken", exprs: [binding("real32:10", "2")] },
      { to: 1, dir: "taken", exprs: [binding("real32:10", "1")] },
    ]);
    expect(split.eiIn).toEqual([]);
  });

  it("includes both successors even when a branch has no expression delta", () => {
    const root = node(0, [binding("real32:10", "0")]);
    const taken = node(1, root.exprs, [0]);
    const notTaken = node(2, root.exprs, [0]);
    expect(splitExprs(root, [root, taken, notTaken], [
      { from: 0, to: 1, dir: "taken" },
      { from: 0, to: 2, dir: "not_taken" },
    ]).eiOut).toEqual([
      { to: 1, dir: "taken", exprs: [] },
      { to: 2, dir: "not_taken", exprs: [] },
    ]);
  });

  it("retains the single-successor and inbound delta behavior", () => {
    const root = node(0, [binding("real32:10", "0")]);
    const child = node(1, [binding("real32:10", "1")], [0]);
    const nodes = [root, child];
    const edges = [{ from: 0, to: 1, dir: "only" }] as const;
    expect(splitExprs(root, nodes, [...edges]).eiOut).toEqual([
      { to: 1, dir: "only", exprs: child.exprs },
    ]);
    expect(splitExprs(child, nodes, [...edges])).toEqual({
      eg: child.exprs, eiOut: [], eiIn: child.exprs,
    });
  });
});
