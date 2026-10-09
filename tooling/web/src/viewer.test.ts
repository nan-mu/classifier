import { describe, expect, it } from "vitest";
import type { PredRow } from "./types";
import { diffPredicates, formatPred, helperName } from "./viewer";

describe("helper predicates", () => {
  it("formats known and unknown helper ids", () => {
    const lookup: PredRow = {
      kind: "helper",
      event: 166,
      helperId: 1,
      args: ["1077412584", "id32(add32(v32:0,4294967280))"],
    };
    expect(helperName(1)).toBe("lookup");
    expect(formatPred(lookup)).toBe(
      "helper lookup@e166(1077412584, id32(add32(v32:0,4294967280)))",
    );
    expect(formatPred({ kind: "helper", helperId: 999, event: 2, args: [] })).toBe(
      "helper helper999@e2()",
    );
  });

  it("diffs helper predicates by event / id / args", () => {
    const a: PredRow[] = [
      { kind: "cmp", rel: "ne", width: 32, lhs: "v32:1", rhs: "0" },
    ];
    const b: PredRow[] = [
      ...a,
      { kind: "helper", event: 4, helperId: 5, args: ["5"] },
    ];
    const d = diffPredicates(a, b);
    expect(d.added).toHaveLength(1);
    expect(d.added[0]!.kind).toBe("helper");
    expect(d.removed).toHaveLength(0);
  });
});
