import { describe, expect, it } from "vitest";
import { formatExprMath } from "./formatExpr";

describe("formatExprMath", () => {
  it("renders ABI names and equality", () => {
    expect(
      formatExprMath({ reg: "real32:10", rel: "eq", term: "7" }),
    ).toBe("a0 = 7");
  });

  it("shortens unsigned compares and map words", () => {
    expect(
      formatExprMath({
        reg: "real32:13",
        rel: "geu",
        term: "18",
        role: "constraint",
      }),
    ).toBe("a3 ≥ᵤ 18");
  });

  it("shows Context cells and create entry inputs; add32 as +", () => {
    expect(
      formatExprMath({
        reg: "context32:0",
        rel: "eq",
        term: "v32:4",
      }),
    ).toBe("ctx.data = data°");
    expect(
      formatExprMath({
        reg: "context32:1",
        rel: "eq",
        term: "add32(v32:4,v32:5)",
      }),
    ).toBe("ctx.end = (data° + len°)");
  });
});
