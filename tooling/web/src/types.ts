export type SessionStatus = "running" | "complete" | "fail";

export type ProgramKind = "esp32c3" | "demo";

export type InsnRow = {
  j: number;
  text: string;
};

export type ExprRow = {
  reg: string;
  rel: string;
  /** Lean pretty-print; treat as opaque string (64-bit safe). */
  term: string;
};

/** Lean cmp/ret JSON; term strings stay opaque (64-bit safe). */
export type PredRow = {
  kind: "cmp" | "ret" | "tag" | "unknown";
  tag?: number;
  rel?: string;
  width?: number;
  lhs?: string;
  rhs?: string;
  /** `kind=ret` observation term. */
  term?: string;
};

export type GraphNode = {
  id: number;
  loc: string;
  exprs: ExprRow[];
  predicates: PredRow[];
  preds: number[];
};

export type GraphEdge = {
  from: number;
  to: number;
  dir: "only" | "taken" | "not_taken";
};

export type LogRow = {
  t: number;
  msg: string;
};

export type SessionSnapshot = {
  id: string;
  status: SessionStatus;
  reason: string | null;
  fuel: number;
  budget: number;
  work: number[];
  focus: number;
  program: ProgramKind;
  insns: InsnRow[];
  nodes: GraphNode[];
  edges: GraphEdge[];
  log: LogRow[];
  cursor_j: number;
  /** Core never claims proof status; UI must show this verbatim. */
  proof_note: string;
};
