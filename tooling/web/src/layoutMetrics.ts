import { foldSameTypeChains, resolveFoldedId } from "./collapse";
import {
  finalizeDisplayLayout,
  GAP_X,
  GAP_Y,
  layoutGraph,
  NODE_H as LAYOUT_NODE_H,
  NODE_W as LAYOUT_NODE_W,
  type NodePosition,
} from "./layout";
import { layoutFinal } from "./layoutFinal";
import { classifyNodeRole, insnTextForNode } from "./nodeRole";
import type { GraphEdge, GraphNode, SessionSnapshot } from "./types";

/** Card footprint used for overlap checks (matches StateNode roughly). */
export const NODE_W = LAYOUT_NODE_W;
export const NODE_H = LAYOUT_NODE_H;

export type Crossing = {
  a: string;
  b: string;
  /** Edge endpoints: from→to. */
  e1: string;
  e2: string;
};

export type StackPair = { a: string; b: string; x: number; y: number };

export type OverlapPair = {
  a: string;
  b: string;
  dx: number;
  dy: number;
};

export type LayoutReport = {
  nodes: number;
  edges: number;
  displayNodes: number;
  displayEdges: number;
  crossings: number;
  stacks: number;
  overlaps: number;
  /** `only` edges whose endpoints differ in y (single-path breaks). */
  onlyBreaks: number;
  gapX: number;
  gapY: number;
  ySpread: number;
  multiYCols: number;
  topCrossings: Crossing[];
  topStacks: StackPair[];
  topOverlaps: OverlapPair[];
  topOnlyBreaks: string[];
};

type Seg = { id: string; x1: number; y1: number; x2: number; y2: number };

function orient(
  ax: number,
  ay: number,
  bx: number,
  by: number,
  cx: number,
  cy: number,
): number {
  return (bx - ax) * (cy - ay) - (by - ay) * (cx - ax);
}

/** Proper segment intersection (shared endpoints do not count). */
export function segmentsCross(s1: Seg, s2: Seg): boolean {
  const ends = new Set([
    `${s1.x1},${s1.y1}`,
    `${s1.x2},${s1.y2}`,
    `${s2.x1},${s2.y1}`,
    `${s2.x2},${s2.y2}`,
  ]);
  // Sharing a vertex → adjacent edges, not a tangle.
  if (ends.size < 4) return false;
  const o1 = orient(s1.x1, s1.y1, s1.x2, s1.y2, s2.x1, s2.y1);
  const o2 = orient(s1.x1, s1.y1, s1.x2, s1.y2, s2.x2, s2.y2);
  const o3 = orient(s2.x1, s2.y1, s2.x2, s2.y2, s1.x1, s1.y1);
  const o4 = orient(s2.x1, s2.y1, s2.x2, s2.y2, s1.x2, s1.y2);
  return o1 * o2 < 0 && o3 * o4 < 0;
}

export function buildDisplayGraph(snap: SessionSnapshot): {
  nodes: GraphNode[];
  edges: GraphEdge[];
} {
  const protectedIds = new Set<number>([snap.focus, ...snap.work]);
  if (snap.status === "fail" && snap.failed != null) protectedIds.add(snap.failed);

  const nodeTypeOf = (id: number): string => {
    const node = snap.nodes.find((n) => n.id === id);
    if (!node) return "";
    return classifyNodeRole({
      node,
      edges: snap.edges,
      insnText: insnTextForNode(node, snap.insns),
      work: snap.work,
      failedId: snap.status === "fail" ? snap.failed : null,
    }).nodeType;
  };

  const fold = foldSameTypeChains(
    snap.nodes,
    snap.edges,
    nodeTypeOf,
    protectedIds,
  );

  const nodes = snap.nodes.filter((n) => !fold.hidden.has(n.id));
  const idSet = new Set(nodes.map((n) => n.id));
  const seen = new Set<string>();
  const edges: GraphEdge[] = [];
  for (const e of snap.edges) {
    if (fold.hidden.has(e.from)) continue;
    const to = resolveFoldedId(e.to, fold);
    if (!idSet.has(e.from) || !idSet.has(to) || e.from === to) continue;
    const key = `${e.from}->${to}:${e.dir}`;
    if (seen.has(key)) continue;
    seen.add(key);
    edges.push(to === e.to ? e : { from: e.from, to, dir: e.dir });
  }
  return { nodes, edges };
}

/**
 * Matches App layout path: d3-dag final pass after complete/fail, otherwise
 * fast spacer layout + column compact.
 */
export function layoutDisplay(
  snap: SessionSnapshot,
  display: { nodes: GraphNode[]; edges: GraphEdge[] },
): Record<string, NodePosition> {
  if (snap.status === "complete" || snap.status === "fail") {
    return layoutFinal(display.nodes, display.edges);
  }
  const full = layoutGraph(snap.nodes, snap.edges);
  return finalizeDisplayLayout(
    full,
    display.nodes.map((n) => String(n.id)),
  );
}
/** @deprecated pin-growth sim; kept for A/B in measure-layout --pins */
export function layoutIncremental(
  nodes: GraphNode[],
  edges: GraphEdge[],
): Record<string, NodePosition> {
  const ids = nodes.map((n) => n.id).sort((a, b) => a - b);
  let pinned: Record<string, NodePosition> = {};
  for (let i = 0; i < ids.length; i++) {
    const slice = new Set(ids.slice(0, i + 1));
    const nSub = nodes.filter((n) => slice.has(n.id));
    const eSub = edges.filter((e) => slice.has(e.from) && slice.has(e.to));
    pinned = layoutGraph(nSub, eSub, pinned);
  }
  return pinned;
}

export function measureLayout(
  positions: Record<string, NodePosition>,
  edges: GraphEdge[],
  opts: { nodeW?: number; nodeH?: number; topN?: number } = {},
): Omit<
  LayoutReport,
  "nodes" | "edges" | "displayNodes" | "displayEdges" | "gapX" | "gapY"
> {
  const nodeW = opts.nodeW ?? NODE_W;
  const nodeH = opts.nodeH ?? NODE_H;
  const topN = opts.topN ?? 12;

  const ids = Object.keys(positions);
  const stacks: StackPair[] = [];
  const overlaps: OverlapPair[] = [];

  for (let i = 0; i < ids.length; i++) {
    for (let j = i + 1; j < ids.length; j++) {
      const a = ids[i]!;
      const b = ids[j]!;
      const pa = positions[a]!;
      const pb = positions[b]!;
      const dx = Math.abs(pa.x - pb.x);
      const dy = Math.abs(pa.y - pb.y);
      if (dx < 1e-6 && dy < 1e-6) {
        stacks.push({ a, b, x: pa.x, y: pa.y });
      } else if (dx < nodeW * 0.85 && dy < nodeH * 0.85) {
        overlaps.push({ a, b, dx, dy });
      }
    }
  }

  const segs: Seg[] = [];
  const onlyBreaks: string[] = [];
  for (const e of edges) {
    if (e.dir === "reuse") continue;
    const from = String(e.from);
    const to = String(e.to);
    const a = positions[from];
    const b = positions[to];
    if (!a || !b) continue;
    segs.push({
      id: `${from}->${to}:${e.dir}`,
      x1: a.x,
      y1: a.y,
      x2: b.x,
      y2: b.y,
    });
    if (e.dir === "only" && Math.abs(a.y - b.y) > 1e-3) {
      onlyBreaks.push(`${from}->${to} Δy=${(b.y - a.y).toFixed(0)}`);
    }
  }

  const crossings: Crossing[] = [];
  for (let i = 0; i < segs.length; i++) {
    for (let j = i + 1; j < segs.length; j++) {
      const s1 = segs[i]!;
      const s2 = segs[j]!;
      if (!segmentsCross(s1, s2)) continue;
      crossings.push({
        a: s1.id,
        b: s2.id,
        e1: s1.id,
        e2: s2.id,
      });
    }
  }

  const ys = ids.map((id) => positions[id]!.y);
  const ySpread = ys.length ? Math.max(...ys) - Math.min(...ys) : 0;
  const byX = new Map<number, number>();
  for (const id of ids) {
    const x = Math.round(positions[id]!.x);
    byX.set(x, (byX.get(x) ?? 0) + 1);
  }
  const multiYCols = [...byX.values()].filter((n) => n > 1).length;

  return {
    crossings: crossings.length,
    stacks: stacks.length,
    overlaps: overlaps.length,
    onlyBreaks: onlyBreaks.length,
    ySpread,
    multiYCols,
    topCrossings: crossings.slice(0, topN),
    topStacks: stacks.slice(0, topN),
    topOverlaps: overlaps.slice(0, topN),
    topOnlyBreaks: onlyBreaks.slice(0, topN),
  };
}

export function reportSnapshot(snap: SessionSnapshot): LayoutReport {
  const display = buildDisplayGraph(snap);
  const positions = layoutDisplay(snap, display);
  const m = measureLayout(positions, display.edges);
  return {
    nodes: snap.nodes.length,
    edges: snap.edges.length,
    displayNodes: display.nodes.length,
    displayEdges: display.edges.length,
    gapX: GAP_X,
    gapY: GAP_Y,
    ...m,
  };
}

export function formatReport(r: LayoutReport): string {
  const lines = [
    `raw=${r.nodes}n/${r.edges}e  display=${r.displayNodes}n/${r.displayEdges}e`,
    `GAP_X=${r.gapX} GAP_Y=${r.gapY}  ySpread=${r.ySpread.toFixed(0)}  multiYCols=${r.multiYCols}`,
    `crossings=${r.crossings}  stacks=${r.stacks}  overlaps=${r.overlaps}  onlyBreaks=${r.onlyBreaks}`,
  ];
  if (r.topStacks.length) {
    lines.push("stacks:");
    for (const s of r.topStacks) {
      lines.push(`  #${s.a} ↔ #${s.b} @ (${s.x},${s.y})`);
    }
  }
  if (r.topOverlaps.length) {
    lines.push("overlaps:");
    for (const o of r.topOverlaps) {
      lines.push(`  #${o.a} ↔ #${o.b} dx=${o.dx.toFixed(0)} dy=${o.dy.toFixed(0)}`);
    }
  }
  if (r.topOnlyBreaks.length) {
    lines.push("onlyBreaks:");
    for (const s of r.topOnlyBreaks) lines.push(`  ${s}`);
  }
  if (r.topCrossings.length) {
    lines.push("crossings:");
    for (const c of r.topCrossings) {
      lines.push(`  ${c.e1}  ×  ${c.e2}`);
    }
  }
  return lines.join("\n");
}
