import {
  coordSimplex,
  dagre,
  decrossTwoLayer,
  sugiyama,
} from "d3-dag";
import { NODE_H, NODE_W, type NodePosition } from "./layout";
import type { GraphEdge, GraphNode } from "./types";

/** Vertical gap between node borders (dagre nodesep). */
const FINAL_NODE_SEP = 14;
/** Horizontal gap for unlabeled ranks. */
const FINAL_RANK_SEP_TIGHT = 28;
/** Horizontal gap when a taken / not_taken edge crosses the rank cut. */
const FINAL_RANK_SEP_LABELED = 72;

/**
 * Offline Sugiyama layout for a finished graph (run-to-completion).
 *
 * Uses d3-dag: two-layer decross + simplex coords, LR. Rank spacing is
 * tight by default and only widened where a branch label must sit.
 */
export function layoutFinal(
  nodes: GraphNode[],
  edges: GraphEdge[],
): Record<string, NodePosition> {
  if (nodes.length === 0) return {};

  const grf = new dagre.graphlib.Graph();
  grf.setGraph({
    rankdir: "LR",
    nodesep: FINAL_NODE_SEP,
    ranksep: FINAL_RANK_SEP_TIGHT,
  });
  grf.setDefaultEdgeLabel(() => ({}));

  for (const n of nodes) {
    grf.setNode(String(n.id), { width: NODE_W, height: NODE_H });
  }

  const layoutEdges: GraphEdge[] = [];
  for (const e of edges) {
    if (e.dir === "reuse") continue;
    const a = String(e.from);
    const b = String(e.to);
    if (a === b) continue;
    if (!grf.hasNode(a) || !grf.hasNode(b)) continue;
    if (grf.hasEdge(a, b)) continue;
    grf.setEdge(a, b);
    layoutEdges.push(e);
  }

  const layout = sugiyama()
    .decross(decrossTwoLayer())
    .coord(coordSimplex());
  dagre.layout(grf, layout);

  const raw: Record<string, { x: number; y: number }> = {};
  for (const n of nodes) {
    const id = String(n.id);
    const p = grf.node(id) as { x?: number; y?: number } | undefined;
    if (p?.x == null || p?.y == null) continue;
    raw[id] = { x: p.x, y: p.y };
  }

  const rankXs = [...new Set(Object.values(raw).map((p) => Math.round(p.x)))].sort(
    (a, b) => a - b,
  );
  const idsByRank = new Map<number, string[]>();
  for (const [id, p] of Object.entries(raw)) {
    const rx = Math.round(p.x);
    const list = idsByRank.get(rx) ?? [];
    list.push(id);
    idsByRank.set(rx, list);
  }

  const labeledCut = new Set<number>();
  for (let i = 0; i < rankXs.length - 1; i++) {
    const left = new Set(idsByRank.get(rankXs[i]!) ?? []);
    const right = new Set(idsByRank.get(rankXs[i + 1]!) ?? []);
    const labeled = layoutEdges.some(
      (e) =>
        (e.dir === "taken" || e.dir === "not_taken") &&
        ((left.has(String(e.from)) && right.has(String(e.to))) ||
          (right.has(String(e.from)) && left.has(String(e.to)))),
    );
    if (labeled) labeledCut.add(i);
  }

  const remap = new Map<number, number>();
  let cursor = rankXs[0] ?? 0;
  for (let i = 0; i < rankXs.length; i++) {
    if (i === 0) {
      remap.set(rankXs[0]!, cursor);
      continue;
    }
    const sep = labeledCut.has(i - 1) ? FINAL_RANK_SEP_LABELED : FINAL_RANK_SEP_TIGHT;
    cursor += NODE_W + sep;
    remap.set(rankXs[i]!, cursor);
  }

  const out: Record<string, NodePosition> = {};
  for (const [id, p] of Object.entries(raw)) {
    const cx = remap.get(Math.round(p.x)) ?? p.x;
    out[id] = { x: cx - NODE_W / 2, y: p.y - NODE_H / 2 };
  }
  return out;
}
