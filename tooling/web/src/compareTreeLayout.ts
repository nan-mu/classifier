import type { TreeNode, TreeReport } from "./types";

/** Column stride between depth ranks. */
export const COMPARE_GAP_X = 380;
/** Vertical stride between consecutive leaves. */
export const COMPARE_GAP_Y = 168;

/**
 * Layered tree layout with contiguous taken / not_taken subtrees.
 * Leaves are ordered by DFS (taken before not_taken); parents sit at the
 * midpoint of their children. That keeps fork edges from crossing on a tree.
 */
export function layoutCompareTree(
  nodes: TreeNode[],
  edges: TreeReport["edges"],
): Record<string, { x: number; y: number }> {
  if (nodes.length === 0) return {};
  const ids = nodes.map((n) => String(n.id));
  const idSet = new Set(ids);
  const children = new Map<string, string[]>();
  const indeg = new Map<string, number>();
  const edgeDir = new Map<string, string>();

  for (const id of ids) {
    children.set(id, []);
    indeg.set(id, 0);
  }
  for (const e of edges) {
    const from = String(e.from);
    const to = String(e.to);
    if (!idSet.has(from) || !idSet.has(to) || from === to) continue;
    children.get(from)!.push(to);
    indeg.set(to, (indeg.get(to) ?? 0) + 1);
    edgeDir.set(`${from}->${to}`, e.dir);
  }
  for (const id of ids) {
    children.get(id)!.sort((a, b) => {
      const ra = dirRank(edgeDir.get(`${id}->${a}`));
      const rb = dirRank(edgeDir.get(`${id}->${b}`));
      return ra - rb || Number(a) - Number(b);
    });
  }

  const roots = ids.filter((id) => (indeg.get(id) ?? 0) === 0);
  const orderedRoots = roots.length > 0 ? roots.sort((a, b) => Number(a) - Number(b)) : [ids[0]!];

  const depth = new Map<string, number>();
  const q = [...orderedRoots];
  for (const r of orderedRoots) depth.set(r, 0);
  while (q.length > 0) {
    const id = q.shift()!;
    const d = depth.get(id) ?? 0;
    for (const child of children.get(id) ?? []) {
      // Tree: first visit wins (min depth). Multi-parent edges are rare; keep shallow.
      if (!depth.has(child)) {
        depth.set(child, d + 1);
        q.push(child);
      }
    }
  }
  for (const id of ids) {
    if (!depth.has(id)) depth.set(id, 0);
  }

  const out: Record<string, { x: number; y: number }> = {};
  const nextLeaf = { n: 0 };

  function place(id: string): number {
    const kids = children.get(id) ?? [];
    let y: number;
    if (kids.length === 0) {
      y = nextLeaf.n * COMPARE_GAP_Y;
      nextLeaf.n += 1;
    } else {
      const ys = kids.map((k) => place(k));
      y = (Math.min(...ys) + Math.max(...ys)) / 2;
    }
    out[id] = { x: (depth.get(id) ?? 0) * COMPARE_GAP_X, y };
    return y;
  }

  for (const root of orderedRoots) {
    place(root);
  }
  // Orphans (unreachable from roots): stack below.
  for (const id of ids) {
    if (out[id] === undefined) place(id);
  }

  // Center the whole forest on y = 0.
  const ys = Object.values(out).map((p) => p.y);
  if (ys.length > 0) {
    const mid = (Math.min(...ys) + Math.max(...ys)) / 2;
    for (const id of Object.keys(out)) {
      out[id]!.y -= mid;
    }
  }
  return out;
}

function dirRank(dir: string | undefined): number {
  if (dir === "taken") return 0;
  if (dir === "not_taken") return 1;
  return 2;
}

/** Count pairwise crossings among consecutive-depth edges (for tests). */
export function countLayerCrossings(
  positions: Record<string, { x: number; y: number }>,
  edges: TreeReport["edges"],
): number {
  const byX = new Map<number, string[]>();
  for (const [id, p] of Object.entries(positions)) {
    const bucket = byX.get(p.x) ?? [];
    bucket.push(id);
    byX.set(p.x, bucket);
  }
  for (const layer of byX.values()) {
    layer.sort((a, b) => positions[a]!.y - positions[b]!.y);
  }
  const xs = [...byX.keys()].sort((a, b) => a - b);
  let cross = 0;
  for (let i = 0; i < xs.length - 1; i++) {
    const left = byX.get(xs[i]!)!;
    const right = byX.get(xs[i + 1]!)!;
    const rIndex = new Map(right.map((id, ri) => [id, ri]));
    const pairs: [number, number][] = [];
    for (let li = 0; li < left.length; li++) {
      const from = left[li]!;
      for (const e of edges) {
        if (String(e.from) !== from) continue;
        const ri = rIndex.get(String(e.to));
        if (ri === undefined) continue;
        pairs.push([li, ri]);
      }
    }
    for (let a = 0; a < pairs.length; a++) {
      for (let b = a + 1; b < pairs.length; b++) {
        const [aL, aR] = pairs[a]!;
        const [bL, bR] = pairs[b]!;
        if ((aL - bL) * (aR - bR) < 0) cross += 1;
      }
    }
  }
  return cross;
}
