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
  const iv = reg.lo != null && reg.hi != null ? `[${reg.lo},${reg.hi})` : "";
  if (reg.kind === "real" && reg.index != null) {
    const n = Number(reg.index);
    const name = Number.isInteger(n) && RV32_ABI[n] ? RV32_ABI[n]! : `x${reg.index}`;
    return `${name}${iv}`;
  }
  if (reg.kind === "stack") return `stack${iv}`;
  if (reg.kind === "context" && reg.field != null) return `ctx.${reg.field}${iv}`;
  if (reg.kind === "map" && reg.index != null) return `M${reg.index}${iv}`;
  if (reg.kind === "packet") return `packet${iv}`;
  return reg.raw;
}

/** Remaining create EntryVar ids (RV32IMC/Initial.lean) — not callee-saved invent-V. */
function entryVarLabel(ξ: number): string | null {
  const named: Record<number, string> = {
    0: "sp°",
    1: "ctx°",
    4: "data°",
    5: "len°",
  };
  return named[ξ] ?? null;
}

const INFIX_OP: Record<string, string> = {
  add32: "+",
  add64: "+",
  sub32: "-",
  sub64: "-",
};

/** Pretty view for chips; wire terms stay add32(…). */
function prettyTerm(view: ReturnType<typeof parseTerm>): string {
  if (view.kind === "const") return view.digits;
  if (view.kind === "var") {
    const n = Number(view.name);
    if (Number.isInteger(n)) {
      const entry = entryVarLabel(n);
      if (entry) return entry;
    }
    return `v${view.name}`;
  }
  if (view.kind === "app" && view.op.startsWith("regVar") && view.args[0]?.kind === "raw") {
    return shortReg(parseReg(view.args[0].text));
  }
  if (view.kind === "app" && INFIX_OP[view.op] && view.args.length === 2) {
    const op = INFIX_OP[view.op]!;
    return `(${prettyTerm(view.args[0]!)} ${op} ${prettyTerm(view.args[1]!)})`;
  }
  if (view.kind === "app") {
    return `${view.op.replace(/32$/, "")}(${view.args.map(prettyTerm).join(", ")})`;
  }
  return termToPlain(view);
}

function shortTerm(term: string): string {
  const plain = prettyTerm(parseTerm(term));
  return plain.length > 36 ? `${plain.slice(0, 34)}…` : plain;
}

/** Compact math line for an Expr row, e.g. `a0 = 7`. */
export function formatExprMath(e: ExprRow): string {
  const left = shortReg(parseReg(e.reg));
  const op = REL_SYM[e.rel] ?? e.rel;
  return `${left} ${op} ${shortTerm(e.term)}`;
}

/** Compact predicate chip text (`formatPred` already shortens helper args). */
export function formatPredChip(p: PredRow): string {
  const s = formatPred(p);
  return s.length > 48 ? `${s.slice(0, 46)}…` : s;
}
