import { describe, expect, it } from "vitest";
import { FORK_SPLIT, layoutGraph } from "./layout";
import type { GraphEdge, GraphNode } from "./types";

const node = (id: number): GraphNode => ({
  id,
  loc: String(id),
  exprs: [],
  predicates: [],
  preds: [],
});

const e = (from: number, to: number, dir: GraphEdge["dir"] = "only"): GraphEdge => ({
  from,
  to,
  dir,
});

describe("layoutGraph (crossing-first)", () => {
  it("keeps a single only-path on one y", () => {
    const pos = layoutGraph(
      [node(0), node(1), node(2), node(3)],
      [e(0, 1), e(1, 2), e(2, 3)],
    );
    expect(pos["0"]!.y).toBeCloseTo(pos["3"]!.y, 5);
    expect(pos["1"]!.y).toBeCloseTo(pos["3"]!.y, 5);
    expect(pos["2"]!.y).toBeCloseTo(pos["3"]!.y, 5);
  });

  it("splits Taken/NotTaken about the parent", () => {
    const pos = layoutGraph(
      [node(0), node(20), node(21)],
      [e(0, 20, "taken"), e(0, 21, "not_taken")],
    );
    expect(pos["20"]!.y).toBeCloseTo(pos["0"]!.y - FORK_SPLIT, 5);
    expect(pos["21"]!.y).toBeCloseTo(pos["0"]!.y + FORK_SPLIT, 5);
  });

  it("lets each arm continue on its own band", () => {
    const pos = layoutGraph(
      [node(0), node(18), node(20), node(24), node(28)],
      [
        e(0, 18, "taken"),
        e(0, 20, "not_taken"),
        e(18, 24),
        e(20, 28),
      ],
    );
    expect(pos["24"]!.y).toBeCloseTo(pos["18"]!.y, 5);
    expect(pos["28"]!.y).toBeCloseTo(pos["20"]!.y, 5);
  });

  it("ignores reuse edges for depth", () => {
    const pos = layoutGraph(
      [node(0), node(1), node(2)],
      [e(0, 1), e(1, 2), e(2, 0, "reuse")],
    );
    expect(pos["2"]!.x).toBeGreaterThan(pos["1"]!.x);
  });

  it("does not move pinned ancestors when new fork arms appear", () => {
    const trunk = layoutGraph(
      [node(0), node(1), node(2)],
      [e(0, 1), e(1, 2)],
    );
    const grown = layoutGraph(
      [node(0), node(1), node(2), node(3), node(4)],
      [e(0, 1), e(1, 2), e(2, 3, "taken"), e(2, 4, "not_taken")],
      trunk,
    );
    expect(grown["0"]!.y).toBe(trunk["0"]!.y);
    expect(grown["2"]!.y).toBe(trunk["2"]!.y);
    expect(grown["3"]!.y).toBeLessThan(grown["2"]!.y);
    expect(grown["4"]!.y).toBeGreaterThan(grown["2"]!.y);
  });
});
