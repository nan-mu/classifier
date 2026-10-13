import type { GraphEdge, GraphNode } from "./types";

export type NodePosition = {
  x: number;
  y: number;
};

/** Footprint matches compact StateNode (~196×~70). */
export const NODE_W = 200;
/** Column stride for unlabeled `only` edges (tight). */
export const GAP_X = 220;
/** Wider column stride when the hop carries a branch label. */
export const GAP_X_LABELED = 280;
/** Card height / same-column clearance. */
export const NODE_H = 72;
export const GAP_Y = NODE_H;
/**
 * Fork offset d: parent at y → arms at y±d (h1/2 < d ≤ h1).
 * Same-row packing is allowed when it helps crossings.
 */
export const FORK_SPLIT = 48;
/** Nudge step when prefer collides: try prefer ± n·k. */
export const NUDGE_K = 16;

const BARY_PASSES = 16;
const TRANSPOSE_PASSES = 12;

function isLayoutEdge(edge: GraphEdge): boolean {
  return edge.dir !== "reuse";
}

/**
 * Crossing-first L→R layout.
 *
 * Minimize edge crossings first; same-column rows are fine when useful.
 * Barycenter + transpose set layer order; Y follows parent/child prefer
 * (only → parent.y, fork → ±d) with ±n·k nudges on collision — no post
 * passes that inflate crossings (chain align / parent recenter / y-swaps).
 */
export function layoutGraph(
  nodes: GraphNode[],
  edges: GraphEdge[],
  pinned: Record<string, NodePosition> = {},
): Record<string, NodePosition> {
  if (nodes.length === 0) return {};

  const realIds = nodes.map((n) => String(n.id));
  const idSet = new Set(realIds);
  const children = new Map<string, string[]>();
  const parents = new Map<string, string[]>();
  const indeg = new Map<string, number>();
  const edgeDir = new Map<string, GraphEdge["dir"]>();

  for (const id of realIds) {
    children.set(id, []);
    parents.set(id, []);
    indeg.set(id, 0);
  }

  type Hop = { from: string; to: string; dir: GraphEdge["dir"] };
  const hops: Hop[] = [];
  for (const edge of edges) {
    if (!isLayoutEdge(edge)) continue;
    const from = String(edge.from);
    const to = String(edge.to);
    if (!idSet.has(from) || !idSet.has(to) || from === to) continue;
    hops.push({ from, to, dir: edge.dir });
    children.get(from)!.push(to);
    parents.get(to)!.push(from);
    indeg.set(to, (indeg.get(to) ?? 0) + 1);
    edgeDir.set(`${from}->${to}`, edge.dir);
  }

  for (const id of realIds) {
    children.get(id)!.sort((a, b) => {
      const da = edgeDir.get(`${id}->${a}`) ?? "only";
      const db = edgeDir.get(`${id}->${b}`) ?? "only";
      return branchRank(da) - branchRank(db) || Number(a) - Number(b);
    });
  }

  const roots = realIds.filter((id) => (indeg.get(id) ?? 0) === 0);
  const startIds = roots.length > 0 ? roots : [realIds[0]!];

  const depth = new Map<string, number>();
  const queue = [...startIds];
  for (const r of startIds) depth.set(r, 0);
  while (queue.length > 0) {
    const id = queue.shift()!;
    const d = depth.get(id) ?? 0;
    for (const child of children.get(id) ?? []) {
      const next = d + 1;
      const prev = depth.get(child);
      if (prev === undefined || next > prev) {
        depth.set(child, next);
        queue.push(child);
      }
    }
  }
  for (const id of realIds) {
    if (!depth.has(id)) depth.set(id, 0);
  }

  let dummySeq = 0;
  const allIds = [...realIds];
  const succ = new Map<string, string[]>();
  const pred = new Map<string, string[]>();
  const hopDir = new Map<string, GraphEdge["dir"]>();
  const ensure = (id: string) => {
    if (!succ.has(id)) {
      succ.set(id, []);
      pred.set(id, []);
    }
  };
  for (const id of realIds) ensure(id);
  const link = (from: string, to: string, dir: GraphEdge["dir"]) => {
    ensure(from);
    ensure(to);
    succ.get(from)!.push(to);
    pred.get(to)!.push(from);
    hopDir.set(`${from}->${to}`, dir);
  };

  for (const h of hops) {
    const d0 = depth.get(h.from)!;
    const d1 = depth.get(h.to)!;
    if (d1 <= d0 + 1) {
      link(h.from, h.to, h.dir);
      continue;
    }
    let prev = h.from;
    for (let d = d0 + 1; d < d1; d++) {
      const dum = `__d${dummySeq++}`;
      allIds.push(dum);
      depth.set(dum, d);
      ensure(dum);
      link(prev, dum, d === d0 + 1 ? h.dir : "only");
      prev = dum;
    }
    link(prev, h.to, "only");
  }

  const maxDepth = Math.max(0, ...allIds.map((id) => depth.get(id) ?? 0));
  const layers: string[][] = Array.from({ length: maxDepth + 1 }, () => []);
  for (const id of allIds) layers[depth.get(id) ?? 0]!.push(id);

  const seed = new Map<string, number>();
  let seq = 0;
  const bfs = [...startIds];
  const seen = new Set(startIds);
  while (bfs.length > 0) {
    const id = bfs.shift()!;
    seed.set(id, seq++);
    const outs = [...(succ.get(id) ?? [])].sort((a, b) => {
      const da = hopDir.get(`${id}->${a}`) ?? "only";
      const db = hopDir.get(`${id}->${b}`) ?? "only";
      return branchRank(da) - branchRank(db) || a.localeCompare(b);
    });
    for (const c of outs) {
      if (seen.has(c)) continue;
      seen.add(c);
      bfs.push(c);
    }
  }
  for (const id of allIds) {
    if (!seed.has(id)) seed.set(id, seq++);
  }
  for (const layer of layers) {
    layer.sort((a, b) => (seed.get(a) ?? 0) - (seed.get(b) ?? 0));
  }

  for (let pass = 0; pass < BARY_PASSES; pass++) {
    if (pass % 2 === 0) {
      for (let d = 1; d <= maxDepth; d++) {
        layers[d] = orderByBary(layers[d]!, layers[d - 1]!, pred);
      }
    } else {
      for (let d = maxDepth - 1; d >= 0; d--) {
        layers[d] = orderByBary(layers[d]!, layers[d + 1]!, succ);
      }
    }
  }
  transposeLayers(layers, succ);

  const positions: Record<string, NodePosition> = {};
  const yOf = new Map<string, number>();
  const pinnedSet = new Set(Object.keys(pinned));
  const orderIndex = new Map<string, number>();
  for (const layer of layers) {
    layer.forEach((id, i) => orderIndex.set(id, i));
  }

  for (const id of realIds) {
    const pin = pinned[id];
    if (!pin) continue;
    positions[id] = { x: pin.x, y: pin.y };
    yOf.set(id, pin.y);
  }

  for (let sweep = 0; sweep < 2; sweep++) {
    const depths =
      sweep === 0
        ? Array.from({ length: maxDepth + 1 }, (_, i) => i)
        : Array.from({ length: maxDepth + 1 }, (_, i) => maxDepth - i);
    for (const d of depths) {
      const colX = d * GAP_X;
      // Place in bary order so collision nudges prefer that reading order.
      for (const id of layers[d]!) {
        if (id.startsWith("__d") || pinnedSet.has(id)) continue;
        const prefer = preferredY(id, parents, children, yOf, edgeDir);
        const y = placeAtPrefer(id, colX, prefer, positions, orderIndex);
        positions[id] = { x: colX, y };
        yOf.set(id, y);
      }
    }
  }

  return positions;
}

export function compactColumns(
  positions: Record<string, NodePosition>,
  keepIds: Iterable<string>,
): Record<string, NodePosition> {
  const ids = [...keepIds].filter((id) => positions[id]);
  if (ids.length === 0) return {};
  const xs = [...new Set(ids.map((id) => Math.round(positions[id]!.x)))].sort(
    (a, b) => a - b,
  );
  const remap = new Map(xs.map((x, i) => [x, i * GAP_X]));
  const out: Record<string, NodePosition> = {};
  for (const id of ids) {
    const p = positions[id]!;
    out[id] = { x: remap.get(Math.round(p.x)) ?? p.x, y: p.y };
  }
  return out;
}

export function finalizeDisplayLayout(
  full: Record<string, NodePosition>,
  displayIds: Iterable<string>,
): Record<string, NodePosition> {
  return compactColumns(full, displayIds);
}

function gapForDir(dir: GraphEdge["dir"]): number {
  return dir === "taken" || dir === "not_taken" ? GAP_X_LABELED : GAP_X;
}

/**
 * Cheap placement while the session is still expanding.
 * Keeps prior coordinates; only drops new nodes beside a parent.
 */
export function layoutStreaming(
  nodes: GraphNode[],
  edges: GraphEdge[],
  prev: Record<string, NodePosition> = {},
): Record<string, NodePosition> {
  const keep = new Set(nodes.map((n) => String(n.id)));
  const out: Record<string, NodePosition> = {};
  for (const [id, p] of Object.entries(prev)) {
    if (keep.has(id)) out[id] = p;
  }

  const incoming = new Map<string, { from: string; dir: GraphEdge["dir"] }[]>();
  for (const e of edges) {
    if (!isLayoutEdge(e)) continue;
    const to = String(e.to);
    const from = String(e.from);
    if (!keep.has(to) || !keep.has(from) || from === to) continue;
    const list = incoming.get(to) ?? [];
    list.push({ from, dir: e.dir });
    incoming.set(to, list);
  }

  for (const n of nodes) {
    const id = String(n.id);
    if (out[id]) continue;
    const hops = incoming.get(id) ?? [];
    const parentHop = hops.find((h) => out[h.from]);
    if (parentHop) {
      const parent = out[parentHop.from]!;
      const x = parent.x + gapForDir(parentHop.dir);
      let y = offsetY(parent.y, parentHop.dir);
      for (let nudge = 0; nudge < 32; nudge++) {
        const tryY = y + (nudge === 0 ? 0 : (nudge % 2 === 0 ? 1 : -1) * Math.ceil(nudge / 2) * NUDGE_K);
        if (!collides(id, x, tryY, out)) {
          y = tryY;
          break;
        }
      }
      out[id] = { x, y };
    } else {
      const row = Object.keys(out).length;
      out[id] = { x: 0, y: row * GAP_Y };
    }
  }
  return out;
}

function placeAtPrefer(
  id: string,
  x: number,
  prefer: number,
  positions: Record<string, NodePosition>,
  orderIndex: Map<string, number>,
): number {
  const myOrder = orderIndex.get(id) ?? 0;
  let barySign = 1;
  for (const [oid, p] of Object.entries(positions)) {
    if (oid === id) continue;
    if (Math.round(p.x) !== Math.round(x)) continue;
    if (Math.abs(p.y - prefer) < GAP_Y - 1e-6) {
      barySign = myOrder >= (orderIndex.get(oid) ?? 0) ? 1 : -1;
      break;
    }
  }
  for (let n = 0; n < 64; n++) {
    const deltas =
      n === 0 ? [0] : [barySign * n * NUDGE_K, -barySign * n * NUDGE_K];
    for (const delta of deltas) {
      const y = prefer + delta;
      if (!collides(id, x, y, positions)) return y;
    }
  }
  return prefer + barySign * 64 * NUDGE_K;
}

function collides(
  id: string,
  x: number,
  y: number,
  positions: Record<string, NodePosition>,
): boolean {
  for (const [oid, p] of Object.entries(positions)) {
    if (oid === id) continue;
    if (Math.round(p.x) !== Math.round(x)) continue;
    if (Math.abs(p.y - y) < GAP_Y - 1e-6) return true;
  }
  return false;
}

function preferredY(
  id: string,
  parents: Map<string, string[]>,
  children: Map<string, string[]>,
  yOf: Map<string, number>,
  edgeDir: Map<string, GraphEdge["dir"]>,
): number {
  const fromParents = (parents.get(id) ?? [])
    .filter((p) => yOf.has(p))
    .map((p) => offsetY(yOf.get(p)!, edgeDir.get(`${p}->${id}`) ?? "only"));
  const fromKids = (children.get(id) ?? [])
    .filter((c) => yOf.has(c))
    .map((c) => {
      const dir = edgeDir.get(`${id}->${c}`) ?? "only";
      const cy = yOf.get(c)!;
      if (dir === "taken") return cy + FORK_SPLIT;
      if (dir === "not_taken") return cy - FORK_SPLIT;
      return cy;
    });
  const ys = [...fromParents, ...fromKids];
  if (ys.length === 0) return 0;
  ys.sort((a, b) => a - b);
  return ys[Math.floor((ys.length - 1) / 2)]!;
}

function offsetY(parentY: number, dir: GraphEdge["dir"]): number {
  if (dir === "taken") return parentY - FORK_SPLIT;
  if (dir === "not_taken") return parentY + FORK_SPLIT;
  return parentY;
}

function orderByBary(
  layer: string[],
  refLayer: string[],
  neigh: Map<string, string[]>,
): string[] {
  const index = new Map(refLayer.map((id, i) => [id, i]));
  const scored = layer.map((id, i) => {
    const ns = (neigh.get(id) ?? []).filter((n) => index.has(n));
    const bary =
      ns.length === 0
        ? i
        : ns.reduce((s, n) => s + index.get(n)!, 0) / ns.length;
    return { id, bary, i };
  });
  scored.sort((a, b) => a.bary - b.bary || a.i - b.i);
  return scored.map((s) => s.id);
}

function transposeLayers(
  layers: string[][],
  succ: Map<string, string[]>,
): void {
  for (let pass = 0; pass < TRANSPOSE_PASSES; pass++) {
    let improved = false;
    for (let d = 0; d < layers.length; d++) {
      const layer = layers[d]!;
      for (let i = 0; i < layer.length - 1; i++) {
        const a = layer[i]!;
        const b = layer[i + 1]!;
        const before =
          (d > 0 ? layerCrossings(layers[d - 1]!, layer, succ) : 0) +
          (d + 1 < layers.length
            ? layerCrossings(layer, layers[d + 1]!, succ)
            : 0);
        layer[i] = b;
        layer[i + 1] = a;
        const after =
          (d > 0 ? layerCrossings(layers[d - 1]!, layer, succ) : 0) +
          (d + 1 < layers.length
            ? layerCrossings(layer, layers[d + 1]!, succ)
            : 0);
        if (after < before) improved = true;
        else {
          layer[i] = a;
          layer[i + 1] = b;
        }
      }
    }
    if (!improved) break;
  }
}

function layerCrossings(
  left: string[],
  right: string[],
  succ: Map<string, string[]>,
): number {
  const rIndex = new Map(right.map((id, i) => [id, i]));
  const pairs: [number, number][] = [];
  for (let li = 0; li < left.length; li++) {
    for (const to of succ.get(left[li]!) ?? []) {
      const ri = rIndex.get(to);
      if (ri === undefined) continue;
      pairs.push([li, ri]);
    }
  }
  let cross = 0;
  for (let i = 0; i < pairs.length; i++) {
    const [aL, aR] = pairs[i]!;
    for (let j = i + 1; j < pairs.length; j++) {
      const [bL, bR] = pairs[j]!;
      if ((aL - bL) * (aR - bR) < 0) cross++;
    }
  }
  return cross;
}

function branchRank(dir: GraphEdge["dir"]): number {
  if (dir === "taken") return 0;
  if (dir === "only") return 1;
  if (dir === "not_taken") return 2;
  return 3;
}
