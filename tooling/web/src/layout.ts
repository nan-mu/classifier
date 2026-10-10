import type { GraphEdge, GraphNode } from "./types";

export type NodePosition = {
  x: number;
  y: number;
};

const GAP_X = 220;
const GAP_Y = 150;

/**
 * Layered left-to-right layout. Single paths sit on one horizontal line;
 * siblings at the same depth fan out vertically so nodes never stack.
 */
export function layoutGraph(
  nodes: GraphNode[],
  edges: GraphEdge[],
): Record<string, NodePosition> {
  if (nodes.length === 0) return {};

  const ids = nodes.map((n) => String(n.id));
  const idSet = new Set(ids);
  const children = new Map<string, string[]>();
  const indeg = new Map<string, number>();
  for (const id of ids) {
    children.set(id, []);
    indeg.set(id, 0);
  }
  for (const edge of edges) {
    const from = String(edge.from);
    const to = String(edge.to);
    if (!idSet.has(from) || !idSet.has(to)) continue;
    children.get(from)!.push(to);
    indeg.set(to, (indeg.get(to) ?? 0) + 1);
  }

  const roots = ids.filter((id) => (indeg.get(id) ?? 0) === 0);
  const order = roots.length > 0 ? roots : [ids[0]!];

  const depth = new Map<string, number>();
  const queue: string[] = [...order];
  for (const r of order) depth.set(r, 0);

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

  for (const id of ids) {
    if (!depth.has(id)) depth.set(id, 0);
  }

  const layers = new Map<number, string[]>();
  for (const id of ids) {
    const d = depth.get(id) ?? 0;
    const layer = layers.get(d) ?? [];
    layer.push(id);
    layers.set(d, layer);
  }

  // Stable order within a layer: by numeric id.
  for (const layer of layers.values()) {
    layer.sort((a, b) => Number(a) - Number(b));
  }

  const positions: Record<string, NodePosition> = {};
  for (const [d, layer] of layers) {
    const n = layer.length;
    for (let i = 0; i < n; i++) {
      const id = layer[i]!;
      positions[id] = {
        x: d * GAP_X,
        y: (i - (n - 1) / 2) * GAP_Y,
      };
    }
  }
  return positions;
}
