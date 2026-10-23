/**
 * Boundary parsers for Lean pretty-printed Reg / Term strings.
 * Exchange still carries `term: string`; this tree is a view only.
 * Numeric leaves stay as decimal/hex strings (never JS number) for 64-bit safety.
 */

export type RegKind = "real" | "stack" | "map" | "context" | "packet" | "unknown";

export type ParsedReg = {
  raw: string;
  kind: RegKind;
  /** Half-open bit interval `[lo, hi)`. */
  lo: number | null;
  hi: number | null;
  /** Architecture register number or map id. */
  index: string | null;
  /** Context field name, including `lddw:n` and `mapKeyBytes:n`. */
  field: string | null;
  /** Map key-byte terms, joined by `;` as rendered. */
  keys: string | null;
};

export type TermView =
  | { kind: "const"; digits: string }
  | { kind: "var"; width: 32 | 64 | null; name: string }
  | { kind: "app"; op: string; args: TermView[] }
  | { kind: "raw"; text: string };

const INTERVAL_TAIL = /\[(\d+),(\d+)\)$/;

function unknownReg(raw: string): ParsedReg {
  return { raw, kind: "unknown", lo: null, hi: null, index: null, field: null, keys: null };
}

function intervalAt(text: string): { rest: string; lo: number; hi: number } | null {
  const m = INTERVAL_TAIL.exec(text);
  if (!m || m.index == null) return null;
  return { rest: text.slice(0, m.index), lo: Number(m[1]), hi: Number(m[2]) };
}

/** `real:r:[b,e)`, `stack:[b,e)`, `packet:[b,e)`, `context:field:[b,e)`, `map:m:[b,e):[keys]`. */
export function parseReg(raw: string): ParsedReg {
  const map = /^map:(\d+):\[(\d+),(\d+)\):(.*)$/.exec(raw);
  if (map) {
    return {
      raw,
      kind: "map",
      lo: Number(map[2]),
      hi: Number(map[3]),
      index: map[1]!,
      field: null,
      keys: map[4] ?? "",
    };
  }
  const iv = intervalAt(raw);
  if (!iv || !iv.rest.endsWith(":")) return unknownReg(raw);
  const head = iv.rest.slice(0, -1);
  if (head === "stack" || head === "packet") {
    return { raw, kind: head, lo: iv.lo, hi: iv.hi, index: null, field: null, keys: null };
  }
  if (head.startsWith("real:")) {
    const index = head.slice("real:".length);
    if (!/^\d+$/.test(index)) return unknownReg(raw);
    return { raw, kind: "real", lo: iv.lo, hi: iv.hi, index, field: null, keys: null };
  }
  if (head.startsWith("context:")) {
    const field = head.slice("context:".length);
    if (field.length === 0) return unknownReg(raw);
    return { raw, kind: "context", lo: iv.lo, hi: iv.hi, index: null, field, keys: null };
  }
  return unknownReg(raw);
}

function regText(raw: string): boolean {
  return parseReg(raw).kind !== "unknown";
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
      args: [regText(regArg) ? { kind: "raw", text: regArg } : parseTerm(regArg)],
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
  stack: "Stack",
  map: "Map",
  context: "Context",
  packet: "Packet",
  unknown: "?",
};

/** Display label for a parsed register, including its bit interval. */
export function formatRegLabel(reg: ParsedReg): string {
  if (reg.lo == null || reg.hi == null) return reg.raw;
  const iv = `[${reg.lo},${reg.hi})`;
  switch (reg.kind) {
    case "real":
      return `x${reg.index ?? "?"}${iv}`;
    case "stack":
      return `stack${iv}`;
    case "packet":
      return `packet${iv}`;
    case "context":
      return `ctx.${reg.field ?? "?"}${iv}`;
    case "map":
      return `map${reg.index ?? "?"}${iv}`;
    default:
      return reg.raw;
  }
}

export const REG_KIND_ORDER: RegKind[] = [
  "real",
  "stack",
  "map",
  "context",
  "packet",
  "unknown",
];

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
