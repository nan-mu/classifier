import { describe, expect, it } from "vitest";
import { arrivalPredicates, classifyNodeRole, predChip } from "./nodeRole";
import type { GraphEdge, GraphNode, PredRow } from "./types";

const n = (
  id: number,
  loc: string,
  opts: {
    predicates?: PredRow[];
    exprs?: GraphNode["exprs"];
    preds?: number[];
    merge_reuse_from?: number;
  } = {},
): GraphNode => ({
  id,
  loc,
  exprs: opts.exprs ?? [],
  predicates: opts.predicates ?? [],
  preds: opts.preds ?? [],
  merge_reuse_from: opts.merge_reuse_from,
});

const e = (from: number, to: number, dir: GraphEdge["dir"]): GraphEdge => ({
  from,
  to,
  dir,
});

describe("predChip", () => {
  it("maps five-class predicates to short chips", () => {
    expect(predChip({ kind: "helper" })).toBe("Helper");
    expect(predChip({ kind: "packetWrite" })).toBe("PacketWrite");
    expect(predChip({ kind: "branch", dir: "taken" })).toBe("Taken");
  });
});

describe("arrivalPredicates", () => {
  it("is the predicate delta vs parent (P_i), not P_g", () => {
    const parent = n(0, "0", {
      predicates: [{ kind: "helper" }, { kind: "packetWrite" }],
    });
    const child = n(1, "4", {
      preds: [0],
      predicates: [
        { kind: "helper" },
        { kind: "packetWrite" },
        { kind: "branch", dir: "taken" },
      ],
    });
    expect(arrivalPredicates(child, [parent, child])).toEqual([
      { kind: "branch", dir: "taken" },
    ]);
  });
});

describe("classifyNodeRole", () => {
  it("lists arrival predicate chips as 节点类型", () => {
    const info = classifyNodeRole({
      node: n(4, "12", {
        predicates: [
          { kind: "packetWrite" },
          { kind: "helper" },
          { kind: "ret" },
        ],
      }),
      edges: [],
    });
    expect(info.tags).toEqual(["Ret", "Helper", "PacketWrite"]);
    expect(info.nodeType).toBe("Ret|Helper|PacketWrite");
    expect(info.role).toBe("ret");
  });

  it("does not put P_g history into tags when P_i is empty", () => {
    const parent = n(0, "0", {
      predicates: [
        { kind: "helper" },
        { kind: "packetWrite" },
        { kind: "branch", dir: "taken" },
        { kind: "branch", dir: "not_taken" },
      ],
    });
    const child = n(3, "6", {
      preds: [0],
      predicates: [
        { kind: "helper" },
        { kind: "packetWrite" },
        { kind: "branch", dir: "taken" },
        { kind: "branch", dir: "not_taken" },
      ],
    });
    const info = classifyNodeRole({
      node: child,
      nodes: [parent, child],
      edges: [e(0, 3, "only")],
      insnText: "0006 ADDI a0,a0,1",
    });
    expect(info.tags).toEqual(["步进"]);
    expect(info.tags).not.toContain("Helper");
    expect(info.tags).not.toContain("PacketWrite");
    expect(info.tags).not.toContain("Taken");
    expect(info.tags).not.toContain("ALU");
    expect(info.role).toBe("alu");
  });

  it("ALU colors the node but is not a title chip without P_i", () => {
    const info = classifyNodeRole({
      node: n(4, "12"),
      edges: [],
      insnText: "0010 ADDI x10, x10, 1",
    });
    expect(info.tags).toEqual(["步进"]);
    expect(info.role).toBe("alu");
    expect(info.accessFamily).toBe(false);
  });

  it("memory still sets accessFamily role without inventing 访存 tag", () => {
    const info = classifyNodeRole({
      node: n(4, "12", {
        exprs: [{ reg: "packet32:0", rel: "eq", term: "1" }],
      }),
      edges: [],
      insnText: "0020 LW x10, 0(x11)",
    });
    expect(info.tags).toEqual(["步进"]);
    expect(info.tags).not.toContain("访存");
    expect(info.accessFamily).toBe(true);
    expect(info.role).toBe("reg_packet");
  });

  it("Taken/NotTaken title chips come from P_i branch preds, not inbound edges", () => {
    const edges = [e(1, 2, "taken"), e(1, 3, "not_taken")];
    const fork = n(1, "4");
    const taken = n(2, "8", {
      preds: [1],
      predicates: [{ kind: "branch", dir: "taken" }],
    });
    const fall = n(3, "9", {
      preds: [1],
      predicates: [{ kind: "branch", dir: "not_taken" }],
    });
    expect(classifyNodeRole({ node: fork, nodes: [fork, taken, fall], edges }).tags).toEqual([
      "步进",
    ]);
    expect(classifyNodeRole({ node: fork, nodes: [fork, taken, fall], edges }).role).toBe(
      "branch",
    );
    expect(
      classifyNodeRole({ node: taken, nodes: [fork, taken, fall], edges }).tags,
    ).toContain("Taken");
    expect(
      classifyNodeRole({ node: fall, nodes: [fork, taken, fall], edges }).tags,
    ).toContain("NotTaken");
  });
});
