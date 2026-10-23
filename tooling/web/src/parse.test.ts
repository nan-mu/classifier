import { describe, expect, it } from "vitest";
import {
  formatRegLabel,
  groupExprsByKind,
  parseReg,
  parseTerm,
  termToPlain,
} from "./parse";

describe("interval regs", () => {
  it("parses the five constructors", () => {
    expect(parseReg("real:10:[0,32)")).toMatchObject({
      kind: "real", index: "10", lo: 0, hi: 32,
    });
    expect(parseReg("stack:[0,32)")).toMatchObject({ kind: "stack", lo: 0, hi: 32 });
    expect(parseReg("packet:[8,16)")).toMatchObject({ kind: "packet", lo: 8, hi: 16 });
    expect(parseReg("context:data:[0,32)")).toMatchObject({
      kind: "context", field: "data", lo: 0, hi: 32,
    });
    expect(parseReg("context:lddw:3:[0,64)")).toMatchObject({
      kind: "context", field: "lddw:3", lo: 0, hi: 64,
    });
    expect(parseReg("map:42:[0,32):[1;2]")).toMatchObject({
      kind: "map", index: "42", lo: 0, hi: 32, keys: "[1;2]",
    });
    expect(formatRegLabel(parseReg("real:10:[0,32)"))).toBe("x10[0,32)");
    expect(formatRegLabel(parseReg("packet:[8,16)"))).toBe("packet[8,16)");
  });

  it("rejects anchor and width-tagged spellings", () => {
    expect(parseReg("anchor32:0").kind).toBe("unknown");
    expect(parseReg("packet32:1").kind).toBe("unknown");
    expect(parseReg("stack32:0").kind).toBe("unknown");
    expect(parseReg("real32:10").kind).toBe("unknown");
    expect(parseReg("map64:0").kind).toBe("unknown");
  });
});

describe("parseTerm", () => {
  const data = { kind: "var", width: 32, name: "4" } as const;

  it("parses extract's comma as part of the op name", () => {
    expect(parseTerm("extract0,8(v32:4)")).toEqual({
      kind: "app", op: "extract0,8", args: [data],
    });
  });

  it.each([8, 16])("keeps nested extract0,%i as one zext argument", (bits) => {
    const text = `zext${bits}/32(extract0,${bits}(v32:4))`;
    const view = parseTerm(text);
    expect(view).toEqual({
      kind: "app", op: `zext${bits}/32`,
      args: [{ kind: "app", op: `extract0,${bits}`, args: [data] }],
    });
    expect(termToPlain(view)).toBe(text);
  });

  it("handles nested mergeLow and still splits actual argument separators", () => {
    const view = parseTerm("add32(mergeLow8,32(v32:4,extract0,8(v32:5)),18446744073709551615)");
    expect(view).toEqual({
      kind: "app", op: "add32", args: [
        { kind: "app", op: "mergeLow8,32", args: [
          data,
          { kind: "app", op: "extract0,8", args: [{ kind: "var", width: 32, name: "5" }] },
        ] },
        { kind: "const", digits: "18446744073709551615" },
      ],
    });
  });

  it("handles comma-named ops following a numeric argument", () => {
    expect(parseTerm("add32(14,extract0,8(v32:4))")).toEqual({
      kind: "app", op: "add32", args: [
        { kind: "const", digits: "14" },
        { kind: "app", op: "extract0,8", args: [data] },
      ],
    });
  });

  it("keeps regVar event in the op and preserves the Reg arg", () => {
    const view = parseTerm("regVar166(real:10:[0,32))");
    expect(view).toEqual({
      kind: "app",
      op: "regVar166",
      args: [{ kind: "raw", text: "real:10:[0,32)" }],
    });
    expect(termToPlain(view)).toBe("regVar166(real:10:[0,32))");
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
  it("orders Real / Stack / Map / Context / Packet groups", () => {
    const groups = groupExprsByKind([
      { reg: "packet:[0,8)", rel: "eq", term: "1" },
      { reg: "real:10:[0,32)", rel: "eq", term: "2" },
      { reg: "map:0:[0,32):[]", rel: "eq", term: "regVar1(real:10:[0,32))" },
      { reg: "stack:[0,32)", rel: "eq", term: "3" },
      { reg: "context:data:[0,32)", rel: "eq", term: "v32:4" },
    ]);
    expect(groups.map((g) => g.kind)).toEqual([
      "real",
      "stack",
      "map",
      "context",
      "packet",
    ]);
    expect(groups[2]!.rows[0]!.reg).toBe("map:0:[0,32):[]");
  });
});
