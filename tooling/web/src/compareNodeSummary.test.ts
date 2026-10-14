import { describe, expect, it } from "vitest";
import { alignListEntries, summarizeTreeNode } from "./compareNodeSummary";
import type { ListEntry, TreeNode } from "./types";

function pred(fp: string, kind = "helper"): ListEntry {
  return {
    tag: "pred",
    atom: {
      node_id: 1,
      loc: "0",
      index: 0,
      kind,
      fields: {},
      fingerprint: fp,
    },
  };
}

describe("alignListEntries", () => {
  it("pairs equal fingerprints in order", () => {
    const left: ListEntry[] = [
      { tag: "start", kind: "create" },
      pred("a"),
      pred("b"),
      { tag: "exit" },
    ];
    const right: ListEntry[] = [
      { tag: "start", kind: "create" },
      pred("a"),
      pred("b"),
      { tag: "exit" },
    ];
    const rows = alignListEntries(left, right);
    expect(rows.every((r) => r.status === "both")).toBe(true);
    expect(rows).toHaveLength(4);
  });

  it("marks only-left and only-right inserts", () => {
    const left: ListEntry[] = [pred("a"), pred("x"), pred("b")];
    const right: ListEntry[] = [pred("a"), pred("b")];
    const rows = alignListEntries(left, right);
    expect(rows.map((r) => r.status)).toEqual(["both", "onlyLeft", "both"]);
  });
});

describe("summarizeTreeNode", () => {
  it("reports coverage when one side has an extra pred", () => {
    const node: TreeNode = {
      id: 3,
      start: "taken",
      left: [pred("a"), pred("extra")],
      right: [pred("a")],
    };
    const s = summarizeTreeNode(node);
    expect(s.verdict).toBe("coverage");
    expect(s.both).toBe(1);
    expect(s.onlyLeft).toBe(1);
    expect(s.onlyRight).toBe(0);
  });

  it("LCS keeps left subsequence when right inserts a duplicate key", () => {
    const node: TreeNode = {
      id: 1,
      start: "create",
      left: [
        { tag: "start", kind: "create" },
        pred("a"),
        pred("b"),
        { tag: "exit" },
      ],
      right: [
        { tag: "start", kind: "create" },
        pred("b"),
        pred("a"),
        pred("b"),
        { tag: "exit" },
      ],
    };
    const s = summarizeTreeNode(node);
    expect(s.both).toBe(4);
    expect(s.onlyLeft).toBe(0);
    expect(s.onlyRight).toBe(1);
    expect(s.verdict).toBe("coverage");
    expect(s.aligned.map((r) => r.status)).toEqual([
      "both",
      "onlyRight",
      "both",
      "both",
      "both",
    ]);
  });
});
