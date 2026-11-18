export type AliveNode = {
  id: string;
  location: { function: string; block: string; instr: string | null };
  state: string;
  unroll: number;
  path_condition?: string;
  ir_state?: Record<string, unknown>;
  rocq_ebpf?: unknown;
  rocq_mapping?: { status: string; reason?: string };
  origin_location?: unknown;
};

export type AliveEdge = {
  id: string;
  from: string;
  to: string;
  kind: string;
  guard: string;
  changed?: string[];
  events?: unknown[];
};

export type AliveTerm = { id: string; op: string; args: string[]; sort: { kind: string; width?: number }; digits?: string; symbol?: string; unsupported?: string };

export type AliveGraph = {
  schema?: string;
  schema_version?: number;
  terms?: AliveTerm[];
  memories?: unknown[];
  evidence?: unknown[];
  run: { status: string; truncation: { kind: string; reason: string } };
  coverage: { all_inputs_covered: string; frontier: string[] };
  nodes: AliveNode[];
  edges: AliveEdge[];
};

export const alive2Layout = {
  header: 56,
  toolbar: 48,
  left: 300,
  leftMin: 240,
  leftMax: 420,
  right: 380,
  rightMin: 320,
  rightMax: 520,
  collapse: 1200,
};

export function edgeKinds(graph: AliveGraph): string[] {
  return graph.edges.map((edge) => edge.kind);
}

export function selectedNode(graph: AliveGraph, id: string | null): AliveNode | null {
  if (!id) return graph.nodes[0] ?? null;
  return graph.nodes.find((node) => node.id === id) ?? null;
}
