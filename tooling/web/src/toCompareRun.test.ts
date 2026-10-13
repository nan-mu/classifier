import { describe, expect, it } from "vitest";
import { toCompareRun, toPredRun, toTreeSnap, type SessionSnapshot } from "./types";

function snap(partial: Partial<SessionSnapshot> & Pick<SessionSnapshot, "edges" | "nodes">): SessionSnapshot {
  return {
    id: "s",
    status: "complete",
    reason: null,
    failed: null,
    fuel: 0,
    budget: 8,
    work: [],
    focus: 0,
    arch: "rv32imc",
    program: "just_tx.elf",
    insns: [],
    log: [],
    cursor_j: 0,
    proof_note: "",
    ...partial,
  };
}

describe("toCompareRun", () => {
  it("maps only|taken|not_taken to OK|Taken|NotTaken and renames from/to to src/dst", () => {
    const run = toCompareRun(
      snap({
        nodes: [
          { id: 0, loc: "0", exprs: [], predicates: [], preds: [] },
          { id: 1, loc: "1", exprs: [], predicates: [], preds: [0] },
        ],
        edges: [
          { from: 0, to: 1, dir: "only" },
          { from: 0, to: 2, dir: "taken" },
          { from: 0, to: 3, dir: "not_taken" },
        ],
      }),
    );
    expect(run.edges).toEqual([
      { src: 0, dst: 1, dir: "OK" },
      { src: 0, dst: 2, dir: "Taken" },
      { src: 0, dst: 3, dir: "NotTaken" },
    ]);
  });

  it("drops reuse edges so POST never sends InvalidDirection", () => {
    const run = toCompareRun(
      snap({
        arch: "ebpf",
        nodes: [{ id: 0, loc: "0", exprs: [], predicates: [], preds: [] }],
        edges: [
          { from: 0, to: 1, dir: "only" },
          { from: 1, to: 0, dir: "reuse" },
        ],
      }),
    );
    expect(run.arch).toBe("ebpf");
    expect(run.edges).toEqual([{ src: 0, dst: 1, dir: "OK" }]);
    expect(run.nodes).toEqual([{ id: 0, loc: "0", exprs: [], predicates: [] }]);
  });
});

describe("toPredRun", () => {
  it("keeps only arch and id/loc/predicates per node", () => {
    const run = toPredRun(
      snap({
        arch: "ebpf",
        nodes: [
          {
            id: 3,
            loc: "exit",
            exprs: [{ reg: "r0", rel: "eq", term: "1" }],
            predicates: [{ kind: "ret", term: "1" }],
            preds: [0],
          },
        ],
        edges: [{ from: 0, to: 3, dir: "only" }],
      }),
    );
    expect(run).toEqual({
      arch: "ebpf",
      nodes: [{ id: 3, loc: "exit", predicates: [{ kind: "ret", term: "1" }] }],
    });
  });
});

describe("toTreeSnap", () => {
  it("keeps arch, id/loc/predicates, and from/to/dir edges without reuse", () => {
    const run = toTreeSnap(
      snap({
        arch: "rv32imc",
        nodes: [
          {
            id: 0,
            loc: "0",
            exprs: [{ reg: "r0", rel: "eq", term: "1" }],
            predicates: [{ kind: "branch", dir: "taken", at: "3" }],
            preds: [],
          },
          {
            id: 1,
            loc: "exit",
            exprs: [],
            predicates: [{ kind: "ret", term: "1" }],
            preds: [0],
          },
        ],
        edges: [
          { from: 0, to: 1, dir: "taken" },
          { from: 1, to: 0, dir: "reuse" },
        ],
      }),
    );
    expect(run).toEqual({
      arch: "rv32imc",
      nodes: [
        { id: 0, loc: "0", predicates: [{ kind: "branch", dir: "taken", at: "3" }] },
        { id: 1, loc: "exit", predicates: [{ kind: "ret", term: "1" }] },
      ],
      edges: [{ from: 0, to: 1, dir: "taken" }],
    });
  });
});
