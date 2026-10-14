import { describe, expect, it } from "vitest";
import { countLayerCrossings, layoutCompareTree } from "./compareTreeLayout";
import type { TreeNode, TreeReport } from "./types";

function node(id: number, start: TreeNode["start"] = "taken"): TreeNode {
  return { id, start, left: [], right: [] };
}

describe("layoutCompareTree", () => {
  it("places taken above not_taken without layer crossings", () => {
    const nodes = [
      node(0, "create"),
      node(1, "taken"),
      node(2, "not_taken"),
      node(3, "taken"),
      node(4, "not_taken"),
    ];
    const edges: TreeReport["edges"] = [
      { from: 0, to: 1, dir: "taken" },
      { from: 0, to: 2, dir: "not_taken" },
      { from: 1, to: 3, dir: "taken" },
      { from: 1, to: 4, dir: "not_taken" },
    ];
    const pos = layoutCompareTree(nodes, edges);
    expect(pos["1"]!.y).toBeLessThan(pos["2"]!.y);
    expect(pos["3"]!.y).toBeLessThan(pos["4"]!.y);
    expect(countLayerCrossings(pos, edges)).toBe(0);
  });

  it("keeps a deep binary fork free of crossings", () => {
    const nodes: TreeNode[] = [node(0, "create")];
    const edges: TreeReport["edges"] = [];
    let next = 1;
    const grow = (parent: number, depth: number) => {
      if (depth === 0) return;
      const t = next++;
      const n = next++;
      nodes.push(node(t, "taken"), node(n, "not_taken"));
      edges.push(
        { from: parent, to: t, dir: "taken" },
        { from: parent, to: n, dir: "not_taken" },
      );
      grow(t, depth - 1);
      grow(n, depth - 1);
    };
    grow(0, 3);
    const pos = layoutCompareTree(nodes, edges);
    expect(countLayerCrossings(pos, edges)).toBe(0);
  });
});
