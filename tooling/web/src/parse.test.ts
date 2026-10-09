import { describe, expect, it } from "vitest";
import {
  cantorUnpair,
  formatRegLabel,
  groupExprsByKind,
  parseReg,
  parseTerm,
  termToPlain,
} from "./parse";

describe("cantorUnpair / packet regs", () => {
  it("round-trips Lean Reg.packet pairing", () => {
    for (const [kappa, offset] of [
      [0, 0],
      [1, 0],
      [0, 1],
      [7, 3],
      [2, 40],
    ] as const) {
      const alpha = ((kappa + offset) * (kappa + offset + 1)) / 2 + offset;
      expect(cantorUnpair(alpha)).toEqual({ first: kappa, second: offset });
      const reg = parseReg(`packet32:${alpha}`);
      expect(reg.kind).toBe("packet");
      expect(reg.resource).toBe(kappa);
      expect(reg.offset).toBe(offset);
      expect(formatRegLabel(reg)).toBe(`Packet32 κ=${kappa} off=${offset}`);
    }
  });

  it("rejects packet64 and unknown shapes", () => {
    expect(parseReg("packet64:0").kind).toBe("unknown");
    expect(parseReg("real32:10")).toMatchObject({
      kind: "real",
      width: 32,
      alpha: "10",
      resource: null,
      offset: null,
    });
  });
});

describe("parseTerm", () => {
  it("keeps regVar event in the op and preserves the Reg arg", () => {
    const view = parseTerm("regVar166(real32:10)");
    expect(view).toEqual({
      kind: "app",
      op: "regVar166",
      args: [{ kind: "raw", text: "real32:10" }],
    });
    expect(termToPlain(view)).toBe("regVar166(real32:10)");
  });

  it("parses nested apps used by helper / packet terms", () => {
    const view = parseTerm("externalResult3_0(5,11)");
    expect(view.kind).toBe("app");
    if (view.kind !== "app") return;
    expect(view.op).toBe("externalResult3_0");
    expect(view.args).toEqual([
      { kind: "const", digits: "5" },
      { kind: "const", digits: "11" },
    ]);
  });
});

describe("groupExprsByKind", () => {
  it("orders Real / Stack / Map / Packet groups", () => {
    const groups = groupExprsByKind([
      { reg: "packet32:1", rel: "eq", term: "1" },
      { reg: "real32:10", rel: "eq", term: "2" },
      { reg: "map32:0", rel: "eq", term: "regVar1(real32:10)" },
      { reg: "stack32:0", rel: "eq", term: "3" },
    ]);
    expect(groups.map((g) => g.kind)).toEqual(["real", "stack", "map", "packet"]);
    expect(groups[2]!.rows[0]!.reg).toBe("map32:0");
  });
});
