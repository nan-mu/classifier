import { describe, expect, it } from "vitest";
import { classifyNodeRole, predChip } from "./nodeRole";
import type { GraphEdge, GraphNode, PredRow } from "./types";

const n = (
  id: number,
  loc: string,
  opts: {
    predicates?: PredRow[];
    exprs?: GraphNode["exprs"];
    merge_reuse_from?: number;
  } = {},
): GraphNode => ({
  id,
  loc,
  exprs: opts.exprs ?? [],
  predicates: opts.predicates ?? [],
  preds: [],
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

describe("classifyNodeRole", () => {
  it("lists all predicate chips as 节点类型", () => {
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

  it("tags ALU and uses alu color", () => {
    const info = classifyNodeRole({
      node: n(4, "12"),
      edges: [],
      insnText: "0010 ADDI x10, x10, 1",
    });
    expect(info.tags).toContain("ALU");
    expect(info.role).toBe("alu");
    expect(info.accessFamily).toBe(false);
  });

  it("splits memory by virtual-register target, not bare 访存", () => {
    const info = classifyNodeRole({
      node: n(4, "12", {
        exprs: [{ reg: "packet32:0", rel: "eq", term: "1" }],
      }),
      edges: [],
      insnText: "0020 LW x10, 0(x11)",
    });
    expect(info.tags).toContain("Packet");
    expect(info.tags).not.toContain("访存");
    expect(info.accessFamily).toBe(true);
    expect(info.role).toBe("reg_packet");
  });

  it("adds Taken/NotTaken from edges", () => {
    const edges = [e(1, 2, "taken"), e(1, 3, "not_taken")];
    expect(classifyNodeRole({ node: n(1, "4"), edges }).tags).toContain("Branch");
    expect(classifyNodeRole({ node: n(2, "8"), edges }).tags).toContain("Taken");
  });
});
