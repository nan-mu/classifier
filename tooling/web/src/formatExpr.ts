import { parseReg, parseTerm, termToPlain, type ParsedReg } from "./parse";
import type { ExprRow, PredRow } from "./types";
import { formatPred } from "./viewer";

const RV32_ABI: Record<number, string> = {
  0: "zero",
  1: "ra",
  2: "sp",
  3: "gp",
  4: "tp",
  5: "t0",
  6: "t1",
  7: "t2",
  8: "s0",
  9: "s1",
  10: "a0",
  11: "a1",
  12: "a2",
  13: "a3",
  14: "a4",
  15: "a5",
  16: "a6",
  17: "a7",
  18: "s2",
  19: "s3",
  20: "s4",
  21: "s5",
  22: "s6",
  23: "s7",
  24: "s8",
  25: "s9",
  26: "s10",
  27: "s11",
  28: "t3",
  29: "t4",
  30: "t5",
  31: "t6",
};

const REL_SYM: Record<string, string> = {
  eq: "=",
  ne: "≠",
  lt: "<",
  le: "≤",
  gt: ">",
  ge: "≥",
  ltu: "<ᵤ",
  leu: "≤ᵤ",
  gtu: ">ᵤ",
  geu: "≥ᵤ",
  lts: "<ₛ",
  les: "≤ₛ",
  gts: ">ₛ",
  ges: "≥ₛ",
};

function shortReg(reg: ParsedReg): string {
  if (reg.kind === "real" && reg.alpha != null) {
    const n = Number(reg.alpha);
    if (Number.isInteger(n) && RV32_ABI[n]) return RV32_ABI[n]!;
    return `x${reg.alpha}`;
  }
  if (reg.kind === "stack" && reg.alpha != null) return `sw${reg.alpha}`;
  if ((reg.kind === "map" || reg.kind === "packet") && reg.resource != null && reg.offset != null) {
    const tag = reg.kind === "map" ? "M" : "P";
    return `${tag}[${reg.resource}+${reg.offset}]`;
  }
  if (reg.kind === "map" && reg.alpha != null) return `M:${reg.alpha}`;
  if (reg.kind === "packet" && reg.alpha != null) return `P:${reg.alpha}`;
  return reg.raw;
}

function shortTerm(term: string): string {
  const view = parseTerm(term);
  if (view.kind === "const") return view.digits;
  if (view.kind === "var") return `v${view.name}`;
  if (view.kind === "app" && view.op.startsWith("regVar") && view.args[0]?.kind === "raw") {
    return shortReg(parseReg(view.args[0].text));
  }
  const plain = termToPlain(view);
  return plain.length > 36 ? `${plain.slice(0, 34)}…` : plain;
}

/** Compact math line for an Expr row, e.g. `a0 = 7`. */
export function formatExprMath(e: ExprRow): string {
  const left = shortReg(parseReg(e.reg));
  const op = REL_SYM[e.rel] ?? e.rel;
  return `${left} ${op} ${shortTerm(e.term)}`;
}

/** Compact predicate chip text. */
export function formatPredChip(p: PredRow): string {
  const s = formatPred(p);
  return s.length > 42 ? `${s.slice(0, 40)}…` : s;
}
