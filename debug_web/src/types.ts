export type SessionStatus = "running" | "complete" | "fail";

export type InsnRow = {
  j: number;
  text: string;
};

export type GraphNode = {
  id: number;
  loc: string;
  r: number;
  preds: number[];
  x: number;
  y: number;
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
