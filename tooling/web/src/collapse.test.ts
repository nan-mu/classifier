import { describe, expect, it } from "vitest";
import { foldSameTypeChains, resolveFoldedId } from "./collapse";
import type { GraphEdge, GraphNode } from "./types";

const node = (id: number): GraphNode => ({
  id,
  loc: String(id),
  exprs: [],
  predicates: [],
  preds: [],
});

const e = (from: number, to: number): GraphEdge => ({
  from,
  to,
  dir: "only",
});

describe("foldSameTypeChains", () => {
  it("folds consecutive same 节点类型 on a degree-2 path", () => {
    const types = new Map([
      [0, "入口"],
      [1, "ALU"],
      [2, "ALU"],
      [3, "ALU"],
      [4, "Helper"],
    ]);
    const fold = foldSameTypeChains(
      [node(0), node(1), node(2), node(3), node(4)],
      [e(0, 1), e(1, 2), e(2, 3), e(3, 4)],
      (id) => types.get(id) ?? "",
      new Set(),
    );
    expect(fold.hidden.has(1)).toBe(true);
    expect(fold.hidden.has(2)).toBe(true);
    expect(fold.hidden.has(3)).toBe(false);
    expect(fold.foldedCount.get(3)).toBe(3);
    expect(resolveFoldedId(1, fold)).toBe(3);
  });

  it("does not fold across different node types", () => {
    const types = new Map([
      [1, "ALU"],
      [2, "Packet"],
      [3, "ALU"],
    ]);
    const fold = foldSameTypeChains(
      [node(1), node(2), node(3)],
      [e(1, 2), e(2, 3)],
      (id) => types.get(id) ?? "",
      new Set(),
    );
    expect(fold.hidden.size).toBe(0);
  });

  it("keeps protected ids visible", () => {
    const types = new Map([
      [1, "PacketWrite"],
      [2, "PacketWrite"],
    ]);
    const fold = foldSameTypeChains(
      [node(1), node(2)],
      [e(1, 2)],
      (id) => types.get(id) ?? "",
      new Set([1]),
    );
    expect(fold.hidden.size).toBe(0);
  });
});
