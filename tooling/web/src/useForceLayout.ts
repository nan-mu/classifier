import { useRef } from "react";
import { layoutStreaming, type NodePosition } from "./layout";
import { layoutFinal } from "./layoutFinal";
import type { GraphEdge, GraphNode } from "./types";

const EMPTY_NODES: GraphNode[] = [];
const EMPTY_EDGES: GraphEdge[] = [];

export type ForcePosition = NodePosition;
export type LayoutMode = "fast" | "final";

/**
 * - `fast`: cheap incremental placement while expanding (no full re-layout).
 * - `final`: d3-dag on the folded display graph after run completes.
 */
export function useForceLayout(
  displayNodes: GraphNode[] | undefined,
  displayEdges: GraphEdge[] | undefined,
  resetKey = "",
  mode: LayoutMode = "fast",
  _spacers?: { nodes: GraphNode[]; edges: GraphEdge[] },
): Record<string, ForcePosition> {
  const shownNodes = displayNodes ?? EMPTY_NODES;
  const shownEdges = displayEdges ?? EMPTY_EDGES;

  const prevRef = useRef<Record<string, ForcePosition>>({});
  const keyRef = useRef("");
  const resetRef = useRef(resetKey);
  const modeRef = useRef(mode);

  if (resetKey !== resetRef.current) {
    resetRef.current = resetKey;
    prevRef.current = {};
    keyRef.current = "";
    modeRef.current = mode;
  }

  const key = [
    mode,
    shownNodes.map((n) => n.id).join(","),
    shownEdges.map((e) => `${e.from}->${e.to}:${e.dir}`).join(","),
  ].join("|");

  if (key !== keyRef.current) {
    keyRef.current = key;
    if (mode === "final") {
      // First final pass: full DAG. Later focus/fold changes must not yank
      // every node — only place ids that are still missing.
      if (Object.keys(prevRef.current).length === 0) {
        prevRef.current = layoutFinal(shownNodes, shownEdges);
      } else {
        prevRef.current = layoutStreaming(shownNodes, shownEdges, prevRef.current);
      }
    } else {
      // Keep prior coords across waves; only place newcomers.
      prevRef.current = layoutStreaming(shownNodes, shownEdges, prevRef.current);
    }
    modeRef.current = mode;
  }

  return prevRef.current;
}
