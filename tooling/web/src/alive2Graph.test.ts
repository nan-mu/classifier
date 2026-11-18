import { describe, expect, it } from "vitest";
import { alive2Layout, edgeKinds, selectedNode, type AliveGraph } from "./alive2Graph";

const concrete: AliveGraph = {
  run: { status: "finished", truncation: { kind: "none", reason: "" } },
  coverage: { all_inputs_covered: "not_established", frontier: [] },
  nodes: [
    { id: "n0", location: { function: "branch", block: "entry", instr: null }, state: "normal", unroll: 0 },
    { id: "n3", location: { function: "branch", block: "%yes", instr: "ret" }, state: "exit", unroll: 0 },
  ],
  edges: [
    { id: "e0", from: "n1", to: "n2", kind: "step", guard: "t0" },
    { id: "e2", from: "n2", to: "n3", kind: "taken", guard: "t0" },
  ],
};

describe("alive2 graph view", () => {
  it("keeps the taken edge and does not invent the other side", () => {
    expect(edgeKinds(concrete)).toEqual(["step", "taken"]);
    expect(edgeKinds(concrete)).not.toContain("not_taken");
    expect(concrete.coverage.all_inputs_covered).toBe("not_established");
  });

  it("uses the desktop column sizes from the viewer spec", () => {
    expect(alive2Layout).toMatchObject({
      header: 56,
      toolbar: 48,
      left: 300,
      right: 380,
      collapse: 1200,
    });
  });

  it("selects the requested node", () => {
    expect(selectedNode(concrete, "n3")?.location.block).toBe("%yes");
    expect(selectedNode(concrete, "missing")).toBeNull();
  });
});
