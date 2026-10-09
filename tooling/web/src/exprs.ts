import type { ExprRow, GraphNode } from "./types";

function sameKey(a: ExprRow, b: ExprRow): boolean {
  return a.reg === b.reg && a.rel === b.rel;
}

/** Reconstruct E_i from parent SemState × child SemState (override inverse). */
export function localExprs(eg: ExprRow[], child: ExprRow[]): ExprRow[] {
  return child.filter((ce) => {
    const pe = eg.find((p) => sameKey(p, ce));
    return !pe || pe.term !== ce.term;
  });
}

export type ExprSplit = {
  eg: ExprRow[];
  /** Bindings produced by expanding this node (parent → child). */
  eiOut: ExprRow[];
  /** Bindings written when arriving here from the first parent. */
  eiIn: ExprRow[];
};

/** E_g at η, plus outbound E_i and inbound Δ from parent. */
export function splitExprs(node: GraphNode, nodes: GraphNode[]): ExprSplit {
  const eg = node.exprs;
  const children = nodes.filter((n) => n.preds.includes(node.id));
  const eiOut =
    children.length === 0 ? [] : localExprs(eg, children[0]!.exprs);
  const parent = nodes.find((n) => node.preds.includes(n.id));
  const eiIn = parent ? localExprs(parent.exprs, eg) : [];
  return { eg, eiOut, eiIn };
}

/** Instruction index highlighted for a graph node (`exit` → parent loc). */
export function insnIndexForNode(
  node: GraphNode | null | undefined,
  nodes: GraphNode[],
): number | null {
  if (!node) return null;
  if (node.loc !== "exit") {
    const j = Number(node.loc);
    return Number.isFinite(j) ? j : null;
  }
  for (const pid of node.preds) {
    const parent = nodes.find((n) => n.id === pid);
    if (!parent || parent.loc === "exit") continue;
    const j = Number(parent.loc);
    if (Number.isFinite(j)) return j;
  }
  return null;
}
