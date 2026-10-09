export type SessionStatus = "running" | "complete" | "fail";

/** Currently only RV32IMC expand is wired through Lean. */
export type ArchKind = "rv32imc";

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

/** Lean cmp/ret/helper JSON; term strings stay opaque (64-bit safe). */
export type PredRow = {
  kind: "cmp" | "ret" | "helper" | "tag" | "unknown";
  tag?: number;
  rel?: string;
  width?: number;
  lhs?: string;
  rhs?: string;
  /** `kind=ret` observation term. */
  term?: string;
  event?: number;
  helperId?: number;
  args?: string[];
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
  /** Rejected step's node; null when no step was attempted (e.g. budget exhaustion). */
  failed: number | null;
  fuel: number;
  budget: number;
  work: number[];
  focus: number;
  arch: ArchKind;
  /** Compact XDP ELF display name (just_tx.elf by default). */
  program: string;
  insns: InsnRow[];
  nodes: GraphNode[];
  edges: GraphEdge[];
  log: LogRow[];
  cursor_j: number;
  /** Core never claims proof status; UI must show this verbatim. */
  proof_note: string;
};
