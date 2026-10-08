import {
  forceCollide,
  forceLink,
  forceManyBody,
  forceSimulation,
  forceX,
  forceY,
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

/**
 * Incremental d3-force layout. Keeps existing node positions across steps.
 * New nodes spawn near their parent edge source so the graph does not collapse
 * to the viewport origin on every Expand tick.
 */
export function useForceLayout(
  nodes: GraphNode[],
  edges: GraphEdge[],
): Record<string, ForcePosition> {
  const [positions, setPositions] = useState<Record<string, ForcePosition>>({});
  const simRef = useRef<Simulation<SimNode, SimLink> | null>(null);
  const nodeMapRef = useRef<Map<string, SimNode>>(new Map());
  const posRef = useRef<Record<string, ForcePosition>>({});

  useEffect(() => {
    const map = nodeMapRef.current;
    const known = new Set(nodes.map((n) => String(n.id)));

    for (const id of [...map.keys()]) {
      if (!known.has(id)) map.delete(id);
    }

    const parentOf = new Map<string, string>();
    for (const edge of edges) {
      const child = String(edge.to);
      if (!parentOf.has(child)) parentOf.set(child, String(edge.from));
    }

    let spawned = 0;
    for (const [index, node] of nodes.entries()) {
      const id = String(node.id);
      if (map.has(id)) continue;
      const parentId = parentOf.get(id);
      const parent = parentId ? map.get(parentId) : undefined;
      const sibling = spawned;
      spawned += 1;
      const seed: SimNode = parent
        ? {
            id,
            x: (parent.x ?? 0) + (sibling - 0.5) * 110,
            y: (parent.y ?? 0) + 130,
            vx: 0,
            vy: 0,
          }
        : {
            id,
            x: (index % 4) * 180 - 270,
            y: Math.floor(index / 4) * 140,
            vx: 0,
            vy: 0,
          };
      map.set(id, seed);
    }

    if (map.size === 0) {
      simRef.current?.stop();
      simRef.current = null;
      posRef.current = {};
      setPositions({});
      return;
    }

    const simNodes = [...map.values()];
    const simLinks: SimLink[] = edges.map((edge) => ({
      id: `${edge.from}->${edge.to}`,
      source: String(edge.from),
      target: String(edge.to),
    }));

    const publish = () => {
      const next: Record<string, ForcePosition> = {};
      for (const node of simNodes) {
        next[node.id] = { x: node.x ?? 0, y: node.y ?? 0 };
      }
      posRef.current = next;
      setPositions(next);
    };

    simRef.current?.stop();
    const sim = forceSimulation(simNodes)
      .force(
        "link",
        forceLink<SimNode, SimLink>(simLinks)
          .id((d) => d.id)
          .distance(150)
          .strength(0.7),
      )
      .force("charge", forceManyBody().strength(-280))
      .force("collide", forceCollide(78).strength(0.9))
      // Mild pull toward a layered band instead of collapsing to (0,0).
      .force("x", forceX(0).strength(0.02))
      .force(
        "y",
        forceY<SimNode>((d) => {
          const depth = Number(d.id) || 0;
          return depth * 28;
        }).strength(0.04),
      )
      .velocityDecay(0.4)
      .alpha(spawned > 0 ? 0.45 : 0.12)
      .alphaDecay(0.04);

    sim.on("tick", publish);
    publish();
    simRef.current = sim;

    return () => {
      sim.stop();
    };
  }, [nodes, edges]);

  return positions;
}
