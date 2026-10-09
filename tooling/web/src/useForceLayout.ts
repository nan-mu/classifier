import { useMemo } from "react";
import { layoutGraph, type NodePosition } from "./layout";
import type { GraphEdge, GraphNode } from "./types";

const EMPTY_NODES: GraphNode[] = [];
const EMPTY_EDGES: GraphEdge[] = [];

export type ForcePosition = NodePosition;

/** Stable layered positions; recomputed only when graph structure changes. */
export function useForceLayout(
  nodes: GraphNode[] | undefined,
  edges: GraphEdge[] | undefined,
): Record<string, ForcePosition> {
  const graphNodes = nodes ?? EMPTY_NODES;
  const graphEdges = edges ?? EMPTY_EDGES;
  const key = `${graphNodes.map((n) => n.id).join(",")}|${graphEdges
    .map((e) => `${e.from}->${e.to}`)
    .join(",")}`;

  return useMemo(
    () => layoutGraph(graphNodes, graphEdges),
    // key captures structure; arrays themselves are often new refs each snap.
    // eslint-disable-next-line react-hooks/exhaustive-deps
    [key],
  );
}
