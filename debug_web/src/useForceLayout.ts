import {
  forceCenter,
  forceCollide,
  forceLink,
  forceManyBody,
  forceSimulation,
  type Simulation,
  type SimulationLinkDatum,
  type SimulationNodeDatum,
} from "d3-force";
import { useEffect, useRef, useState } from "react";
import type { GraphEdge, GraphNode } from "./types";

type SimNode = SimulationNodeDatum & {
  id: string;
};

type SimLink = SimulationLinkDatum<SimNode> & {
  id: string;
};

export type ForcePosition = {
  x: number;
  y: number;
};

/** Keep xyflow positions under a d3-force simulation (velocity + acceleration). */
export function useForceLayout(
  nodes: GraphNode[],
  edges: GraphEdge[],
  graphKey: string,
): Record<string, ForcePosition> {
  const [positions, setPositions] = useState<Record<string, ForcePosition>>({});
  const simRef = useRef<Simulation<SimNode, SimLink> | null>(null);
  const prevRef = useRef<Record<string, ForcePosition>>({});
  const nodesRef = useRef(nodes);
  const edgesRef = useRef(edges);
  nodesRef.current = nodes;
  edgesRef.current = edges;

  useEffect(() => {
    const graphNodes = nodesRef.current;
    const graphEdges = edgesRef.current;
    const prior = prevRef.current;
    const simNodes: SimNode[] = graphNodes.map((node, index) => {
      const id = String(node.id);
      const kept = prior[id];
      const angle = (index / Math.max(graphNodes.length, 1)) * Math.PI * 2;
      return {
        id,
        x: kept?.x ?? Math.cos(angle) * 140,
        y: kept?.y ?? Math.sin(angle) * 140,
        vx: 0,
        vy: 0,
      };
    });

    const simLinks: SimLink[] = graphEdges.map((edge) => ({
      id: `${edge.from}-${edge.to}`,
      source: String(edge.from),
      target: String(edge.to),
    }));

    simRef.current?.stop();
    const sim = forceSimulation(simNodes)
      .force(
        "link",
        forceLink<SimNode, SimLink>(simLinks)
          .id((d) => d.id)
          .distance(128)
          .strength(0.55),
      )
      .force("charge", forceManyBody().strength(-420))
      .force("center", forceCenter(0, 0).strength(0.06))
      .force("collide", forceCollide(72).strength(0.85))
      .velocityDecay(0.28)
      .alpha(0.9)
      .alphaDecay(0.028);

    sim.on("tick", () => {
      const next: Record<string, ForcePosition> = {};
      for (const node of simNodes) {
        next[node.id] = { x: node.x ?? 0, y: node.y ?? 0 };
      }
      prevRef.current = next;
      setPositions(next);
    });

    simRef.current = sim;
    return () => {
      sim.stop();
    };
  }, [graphKey]);

  return positions;
}
