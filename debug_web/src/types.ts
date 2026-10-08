export type SessionStatus = "running" | "complete" | "fail";

export type InsnRow = {
  j: number;
  text: string;
};

export type ExprRow = {
  reg: string;
  rel: string;
  term: string;
};

export type PredRow = {
  tag: number;
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
  insns: InsnRow[];
  nodes: GraphNode[];
  edges: GraphEdge[];
  log: LogRow[];
  cursor_j: number;
};
