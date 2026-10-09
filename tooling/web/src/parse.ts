/**
 * Boundary parsers for Lean pretty-printed Reg / Term strings.
 * Exchange still carries `term: string`; this tree is a view only.
 * Numeric leaves stay as decimal/hex strings (never JS number) for 64-bit safety.
 */

export type RegKind = "real" | "stack" | "map" | "packet" | "unknown";

export type ParsedReg = {
  raw: string;
  kind: RegKind;
  width: 32 | 64 | null;
  alpha: string | null;
  /** Namespace from Cantor unpair for Packet bytes and Map32 lookup words. */
  resource: number | null;
  /** Byte offset from Cantor unpair for Packet bytes and Map32 lookup words. */
  offset: number | null;
};

export type TermView =
  | { kind: "const"; digits: string }
  | { kind: "var"; width: 32 | 64 | null; name: string }
  | { kind: "app"; op: string; args: TermView[] }
  | { kind: "raw"; text: string };

const REG_RE = /^(real|stack|map|packet)(32|64):(\d+)$/;

/** Inverse of Lean `Reg.packet` / `Reg.mapWord` pairing: α = T_{κ+off} + off. */
export function cantorUnpair(alpha: number): { first: number; second: number } | null {
  if (!Number.isInteger(alpha) || alpha < 0 || !Number.isSafeInteger(alpha)) {
    return null;
  }
  const w = Math.floor((Math.sqrt(8 * alpha + 1) - 1) / 2);
  const triangle = (w * (w + 1)) / 2;
  const second = alpha - triangle;
  const first = w - second;
  if (!Number.isInteger(second) || second < 0 || first < 0) return null;
  if ((first + second) * (first + second + 1) / 2 + second !== alpha) return null;
  return { first, second };
}

export function parseReg(raw: string): ParsedReg {
  const m = REG_RE.exec(raw);
  if (!m || (m[1] === "packet" && m[2] !== "32")) {
    return {
      raw,
      kind: "unknown",
      width: null,
      alpha: null,
      resource: null,
      offset: null,
    };
  }
  const kind = m[1] as RegKind;
  const alpha = m[3]!;
  let resource: number | null = null;
  let offset: number | null = null;
  if (kind === "packet" || (kind === "map" && m[2] === "32")) {
    const pair = cantorUnpair(Number(alpha));
    if (pair) {
      resource = pair.first;
      offset = pair.second;
    }
  }
  return {
    raw,
    kind,
    width: Number(m[2]) as 32 | 64,
    alpha,
    resource,
    offset,
  };
}

function splitTopArgs(body: string): string[] {
  const out: string[] = [];
  let depth = 0;
  let start = 0;
  for (let i = 0; i < body.length; i++) {
    const ch = body[i]!;
    if (ch === "(") depth += 1;
    else if (ch === ")") depth -= 1;
    else if (ch === "," && depth === 0) {
      // Lean's extract and mergeLow names contain a numeric comma before their opening parenthesis.
      if (
        /^(?:extract|mergeLow)\d+$/.test(body.slice(start, i).trim()) &&
        /^\d+\(/.test(body.slice(i + 1))
      ) continue;
      out.push(body.slice(start, i));
      start = i + 1;
    }
  }
  if (start <= body.length) out.push(body.slice(start));
  return out.filter((s) => s.length > 0);
}

/** Best-effort Term tree from Lean `renderTerm` text. */
export function parseTerm(text: string): TermView {
  const t = text.trim();
  if (/^\d+$/.test(t) || /^0x[0-9a-fA-F]+$/.test(t)) {
    return { kind: "const", digits: t };
  }
  const varM = /^v(32|64):(\d+)$/.exec(t);
  if (varM) {
    return { kind: "var", width: Number(varM[1]) as 32 | 64, name: varM[2]! };
  }
  // regVar{event}(reg) — event is part of the op name; arg is a Reg string.
  const regVarM = /^regVar(\d+)\((.+)\)$/.exec(t);
  if (regVarM) {
    const regArg = regVarM[2]!;
    return {
      kind: "app",
      op: `regVar${regVarM[1]}`,
      args: [REG_RE.test(regArg) ? { kind: "raw", text: regArg } : parseTerm(regArg)],
    };
  }
  const open = t.indexOf("(");
  if (open > 0 && t.endsWith(")")) {
    const op = t.slice(0, open);
    const body = t.slice(open + 1, -1);
    return { kind: "app", op, args: splitTopArgs(body).map(parseTerm) };
  }
  return { kind: "raw", text: t };
}

export function termToPlain(view: TermView): string {
  switch (view.kind) {
    case "const":
      return view.digits;
    case "var":
      return view.width ? `v${view.width}:${view.name}` : `v?:${view.name}`;
    case "app":
      return `${view.op}(${view.args.map(termToPlain).join(",")})`;
    case "raw":
      return view.text;
  }
}

export const kindLabel: Record<RegKind, string> = {
  real: "Real",
  stack: "Stack(SW)",
  map: "Map",
  packet: "Packet",
  unknown: "?",
};

/** Display label for a parsed register, including paired namespaces and offsets. */
export function formatRegLabel(reg: ParsedReg): string {
  const kind = kindLabel[reg.kind];
  const w = reg.width ?? "?";
  if ((reg.kind === "packet" || reg.kind === "map") && reg.resource != null && reg.offset != null) {
    return `${kind}${w} κ=${reg.resource} off=${reg.offset}`;
  }
  return `${kind}${w} α=${reg.alpha ?? "?"}`;
}

export const REG_KIND_ORDER: RegKind[] = ["real", "stack", "map", "packet", "unknown"];

export function groupExprsByKind<T extends { reg: string }>(
  exprs: T[],
): { kind: RegKind; rows: T[] }[] {
  const buckets = new Map<RegKind, T[]>();
  for (const kind of REG_KIND_ORDER) buckets.set(kind, []);
  for (const row of exprs) {
    const kind = parseReg(row.reg).kind;
    buckets.get(kind)!.push(row);
  }
  return REG_KIND_ORDER.filter((kind) => (buckets.get(kind)?.length ?? 0) > 0).map(
    (kind) => ({ kind, rows: buckets.get(kind)! }),
  );
}
