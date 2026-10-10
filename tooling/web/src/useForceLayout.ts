import { useRef } from "react";
import { layoutGraph, type NodePosition } from "./layout";
import type { GraphEdge, GraphNode } from "./types";

const EMPTY_NODES: GraphNode[] = [];
const EMPTY_EDGES: GraphEdge[] = [];

export type ForcePosition = NodePosition;

/**
 * Layered positions. Existing node ids keep their coordinates across graph growth
 * so streaming expand does not reshuffle the whole canvas; only new ids are placed.
 * Pass a new `resetKey` (e.g. session id) to drop the cache.
 */
export function useForceLayout(
  nodes: GraphNode[] | undefined,
  edges: GraphEdge[] | undefined,
  resetKey = "",
): Record<string, ForcePosition> {
  const graphNodes = nodes ?? EMPTY_NODES;
  const graphEdges = edges ?? EMPTY_EDGES;
  const prevRef = useRef<Record<string, ForcePosition>>({});
  const keyRef = useRef("");
  const resetRef = useRef(resetKey);

  if (resetKey !== resetRef.current) {
    resetRef.current = resetKey;
    prevRef.current = {};
    keyRef.current = "";
  }

  const key = `${graphNodes.map((n) => n.id).join(",")}|${graphEdges
    .map((e) => `${e.from}->${e.to}`)
    .join(",")}`;

  if (key !== keyRef.current) {
    keyRef.current = key;
    const fresh = layoutGraph(graphNodes, graphEdges);
    const merged: Record<string, ForcePosition> = {};
    for (const node of graphNodes) {
      const id = String(node.id);
      merged[id] = prevRef.current[id] ?? fresh[id] ?? { x: 0, y: 0 };
    }
    prevRef.current = merged;
  }

  return prevRef.current;
}
