/**
 * Boundary parsers for Lean pretty-printed Reg / Term strings.
 * Exchange still carries `term: string`; this tree is a view only.
 * Numeric leaves stay as decimal/hex strings (never JS number) for 64-bit safety.
 */

export type RegKind = "real" | "stack" | "map" | "unknown";

export type ParsedReg = {
  raw: string;
  kind: RegKind;
  width: 32 | 64 | null;
  alpha: string | null;
};

export type TermView =
  | { kind: "const"; digits: string }
  | { kind: "var"; width: 32 | 64 | null; name: string }
  | { kind: "app"; op: string; args: TermView[] }
  | { kind: "raw"; text: string };

const REG_RE = /^(real|stack|map)(32|64):(\d+)$/;

export function parseReg(raw: string): ParsedReg {
  const m = REG_RE.exec(raw);
  if (!m) return { raw, kind: "unknown", width: null, alpha: null };
  return {
    raw,
    kind: m[1] as RegKind,
    width: Number(m[2]) as 32 | 64,
    alpha: m[3]!,
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
  unknown: "?",
};
