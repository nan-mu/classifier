import type { GraphEdge, GraphNode } from "./types";

export type TypeFold = {
  hidden: Set<number>;
  foldedCount: Map<number, number>;
  redirect: Map<number, number>;
};

const EMPTY_FOLD: TypeFold = {
  hidden: new Set(),
  foldedCount: new Map(),
  redirect: new Map(),
};

function structuralEdges(edges: GraphEdge[]): GraphEdge[] {
  return edges.filter((e) => e.dir !== "reuse");
}

/**
 * Compress degree-2 runs whose **节点类型** (first-line tag key) is identical.
 * Always on; protected ids are never hidden.
 */
export function foldSameTypeChains(
  nodes: GraphNode[],
  edges: GraphEdge[],
  nodeTypeOf: (id: number) => string,
  protectedIds: Set<number>,
): TypeFold {
  if (nodes.length === 0) return EMPTY_FOLD;

  const byId = new Map(nodes.map((n) => [n.id, n]));
  const succ = new Map<number, number[]>();
  const pred = new Map<number, number[]>();
  for (const n of nodes) {
    succ.set(n.id, []);
    pred.set(n.id, []);
  }
  for (const e of structuralEdges(edges)) {
    if (!byId.has(e.from) || !byId.has(e.to)) continue;
    succ.get(e.from)!.push(e.to);
    pred.get(e.to)!.push(e.from);
  }

  const foldable = (id: number): boolean => {
    if (protectedIds.has(id)) return false;
    const n = byId.get(id);
    if (!n || n.id === 0 || n.loc === "exit") return false;
    const t = nodeTypeOf(id);
    if (!t || t === "入口" || t === "出口" || t === "拒绝") return false;
    const ins = pred.get(id) ?? [];
    const outs = succ.get(id) ?? [];
    return ins.length === 1 && outs.length === 1;
  };

  const hidden = new Set<number>();
  const foldedCount = new Map<number, number>();
  const redirect = new Map<number, number>();
  const seen = new Set<number>();

  for (const n of nodes) {
    if (!foldable(n.id) || seen.has(n.id)) continue;

    let start = n.id;
    const startType = nodeTypeOf(start);
    while (true) {
      const ps = pred.get(start) ?? [];
      if (ps.length !== 1) break;
      const p = ps[0]!;
      if (!foldable(p) || nodeTypeOf(p) !== startType) break;
      start = p;
    }

    const runType = nodeTypeOf(start);
    const run: number[] = [];
    let cur: number | undefined = start;
    while (cur != null && foldable(cur) && !seen.has(cur) && nodeTypeOf(cur) === runType) {
      run.push(cur);
      seen.add(cur);
      const outs: number[] = succ.get(cur) ?? [];
      const next: number | undefined = outs[0];
      cur =
        next != null && foldable(next) && nodeTypeOf(next) === runType
          ? next
          : undefined;
    }

    if (run.length < 2) continue;
    const rep = run[run.length - 1]!;
    foldedCount.set(rep, run.length);
    for (const id of run) {
      redirect.set(id, rep);
      if (id !== rep) hidden.add(id);
    }
  }

  return { hidden, foldedCount, redirect };
}

export function resolveFoldedId(id: number, fold: TypeFold): number {
  return fold.redirect.get(id) ?? id;
}
