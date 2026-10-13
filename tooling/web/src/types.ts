export type SessionStatus = "running" | "complete" | "fail";

/** Server create accepts both; the single-run select defaults to rv32imc. */
export type ArchKind = "rv32imc" | "ebpf";

export type InsnRow = {
  j: number;
  text: string;
};

export type ExprRow = {
  reg: string;
  rel: string;
  /** Lean pretty-print; treat as opaque string (64-bit safe). */
  term: string;
  role?: "constraint";
};

/**
 * One Predicate observation (opaque five-class kinds: helper, branch, ret,
 * mapWrite / map_write, packetWrite / packet_write, plus mapLookup, …).
 * `kind` is the disjoint-union tag; other fields are kind-specific and opaque.
 * New Lean Predicate variants must not require TS shape changes.
 */
export type PredRow = {
  kind: string;
  [field: string]: unknown;
};

export type GraphNode = {
  id: number;
  loc: string;
  exprs: ExprRow[];
  predicates: PredRow[];
  preds: number[];
  /** Exact-config merge reuse target (NotTaken suffix entry). */
  merge_reuse_from?: number;
};

export type GraphEdge = {
  from: number;
  to: number;
  dir: "only" | "taken" | "not_taken" | "reuse";
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

export type CompareDir = "OK" | "Taken" | "NotTaken";

export type CompareNode = {
  id: number;
  loc: string;
  exprs: ExprRow[];
  predicates: PredRow[];
};

export type CompareEdge = {
  src: number;
  dst: number;
  dir: CompareDir;
};

/** Non-empty `arch`. Empty `nodes` is legal JSON and a Lean `EmptyRun` reject. */
export type CompareRun = {
  arch: string;
  nodes: CompareNode[];
  edges: CompareEdge[];
};

export type CompareRequest = {
  left: CompareRun;
  right: CompareRun;
};

export type ClassName =
  | "valueBindings"
  | "constraints"
  | "helper"
  | "branch"
  | "ret"
  | "mapWrite"
  | "packetWrite";

export type ClassVerdict = "equal" | "AbsentLeft" | "AbsentRight" | "Differs";
export type PositionVerdict = "Both" | "OnlyLeft" | "OnlyRight";
export type ControlVerdict = "equal" | "Differs";
export type CompareConclusion = "sameStructure" | "differs" | "coverageDiffers";

/**
 * `items` in Compare.lean parses each rendered member back to JSON,
 * or leaves a string if that parse fails. Expr rows match `ExprRow`
 * (constraints include `role: "constraint"`). Predicate rows match `PredRow`.
 */
export type ClassMember = ExprRow | PredRow | string;

export type ClassReport = {
  class: ClassName;
  verdict: ClassVerdict;
  leftCount: number;
  rightCount: number;
  onlyLeft: ClassMember[];
  onlyRight: ClassMember[];
};

/** Members are `"<dir>-><loc>"`, e.g. `"Taken->12"`, `"OK->exit"`. */
export type ControlReport = {
  verdict: ControlVerdict;
  membersLeft: string[];
  membersRight: string[];
  onlyLeft: string[];
  onlyRight: string[];
};

/**
 * `control` and `classes` exist only when `verdict == "Both"`.
 * `classes` is then the seven names above, in that order.
 * `OnlyLeft` / `OnlyRight` rows are counts only.
 */
export type PositionReport = {
  loc: string;
  verdict: PositionVerdict;
  leftNodes: number;
  rightNodes: number;
  control?: ControlReport;
  classes?: ClassReport[];
};

export type RunSummary = {
  arch: string;
  nodeCount: number;
  edgeCount: number;
};

export type CompareReport = {
  status: "compared";
  claim: "structural";
  behavioralEquivalence: "notEstablished";
  conclusion: CompareConclusion;
  left: RunSummary;
  right: RunSummary;
  positions: PositionReport[];
  basis: string[];
  openObligations: string[];
};

export type CompareReject = {
  status: "reject";
  reason: "InsufficientEvidence";
  detail: string;
};

export type CompareOutcome = CompareReport | CompareReject;

/** Wire shape for `POST /api/compare/predicates` (id/loc/predicates only). */
export type PredRunNode = {
  id: number;
  loc: string;
  predicates: PredRow[];
};

export type PredRun = {
  arch: string;
  nodes: PredRunNode[];
};

export type SoftScore = {
  kind: number;
  fields: number;
  terms: number;
  overall: number;
};

export type PredAtom = {
  node_id: number;
  loc: string;
  index: number;
  kind: string;
  fields: Record<string, unknown>;
  fingerprint: string;
};

export type PredPair =
  | { status: "matched"; loc: string; score: SoftScore; left: PredAtom; right: PredAtom }
  | { status: "onlyLeft"; loc: string; left: PredAtom }
  | { status: "onlyRight"; loc: string; right: PredAtom };

export type PredLocBucket = {
  loc: string;
  leftCount: number;
  rightCount: number;
  pairs: PredPair[];
};

export type PredRunSummary = {
  arch: string;
  nodeCount: number;
  predCount: number;
};

/** Host fuzzy Predicate align; `claim` stays heuristic until Lean Term equality. */
export type PredMatchReport = {
  status: "matched";
  claim: "heuristic";
  behavioralEquivalence: "notEstablished";
  note: string;
  left: PredRunSummary;
  right: PredRunSummary;
  matched: number;
  only_left: number;
  only_right: number;
  locations: PredLocBucket[];
};

const COMPARE_DIR = {
  only: "OK",
  taken: "Taken",
  not_taken: "NotTaken",
} as const;

/** Strip a session snapshot to the Lean compare wire shape; drop `reuse` edges. */
export function toCompareRun(snap: SessionSnapshot): CompareRun {
  const edges: CompareEdge[] = [];
  for (const e of snap.edges) {
    const dir = COMPARE_DIR[e.dir as keyof typeof COMPARE_DIR];
    if (!dir) continue;
    edges.push({ src: e.from, dst: e.to, dir });
  }
  return {
    arch: snap.arch,
    nodes: snap.nodes.map(({ id, loc, exprs, predicates }) => ({
      id,
      loc,
      exprs,
      predicates,
    })),
    edges,
  };
}

/** Strip a snapshot to PredRun for heuristic Predicate match. */
export function toPredRun(snap: SessionSnapshot): PredRun {
  return {
    arch: snap.arch,
    nodes: snap.nodes.map(({ id, loc, predicates }) => ({ id, loc, predicates })),
  };
}

/** Flatten a PredAtom into a PredRow for formatPred / chips. */
export function atomToPred(atom: PredAtom): PredRow {
  return { kind: atom.kind, ...atom.fields };
}
