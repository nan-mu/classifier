import { Box, Flex, Text } from "@kuma-ui/core";
import {
  Background,
  ConnectionMode,
  Handle,
  Position,
  ReactFlow,
  type Edge,
  type Node,
  type NodeProps,
  type ReactFlowInstance,
} from "@xyflow/react";
import { useCallback, useMemo } from "react";
import { formatPredChip } from "./formatExpr";
import {
  atomToPred,
  type ListEntry,
  type SoftScore,
  type StartKind,
  type TreeNode,
  type TreeReport,
} from "./types";
import { formatPred } from "./viewer";

const NODE_W = 280;
const NODE_H = 120;
const GAP_X = 320;
const GAP_Y = 160;

type TreeFlowData = {
  start: StartKind;
  left: ListEntry[];
  right: ListEntry[];
  tipScore?: SoftScore;
};

type TreeFlowNode = Node<TreeFlowData, "tree">;

function layoutTree(
  nodes: TreeNode[],
  edges: TreeReport["edges"],
): Record<string, { x: number; y: number }> {
  if (nodes.length === 0) return {};
  const ids = nodes.map((n) => String(n.id));
  const idSet = new Set(ids);
  const children = new Map<string, string[]>();
  const indeg = new Map<string, number>();
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
  }
  for (const id of ids) {
    children.get(id)!.sort((a, b) => {
      const ea = edges.find((e) => String(e.from) === id && String(e.to) === a);
      const eb = edges.find((e) => String(e.from) === id && String(e.to) === b);
      const ra = ea?.dir === "taken" ? 0 : 1;
      const rb = eb?.dir === "taken" ? 0 : 1;
      return ra - rb || Number(a) - Number(b);
    });
  }
  const roots = ids.filter((id) => (indeg.get(id) ?? 0) === 0);
  const start = roots.length > 0 ? roots : [ids[0]!];
  const depth = new Map<string, number>();
  const q = [...start];
  for (const r of start) depth.set(r, 0);
  while (q.length > 0) {
    const id = q.shift()!;
    const d = depth.get(id) ?? 0;
    for (const child of children.get(id) ?? []) {
      const next = d + 1;
      const prev = depth.get(child);
      if (prev === undefined || next > prev) {
        depth.set(child, next);
        q.push(child);
      }
    }
  }
  for (const id of ids) {
    if (!depth.has(id)) depth.set(id, 0);
  }
  const layers = new Map<number, string[]>();
  for (const id of ids) {
    const d = depth.get(id) ?? 0;
    const row = layers.get(d) ?? [];
    row.push(id);
    layers.set(d, row);
  }
  const out: Record<string, { x: number; y: number }> = {};
  const maxDepth = Math.max(0, ...depth.values());
  for (let d = 0; d <= maxDepth; d++) {
    const row = (layers.get(d) ?? []).sort((a, b) => Number(a) - Number(b));
    const totalW = Math.max(0, row.length - 1) * GAP_X;
    const x0 = -totalW / 2;
    row.forEach((id, i) => {
      out[id] = { x: x0 + i * GAP_X, y: d * GAP_Y };
    });
  }
  return out;
}

function EntryChip({ entry }: { entry: ListEntry }) {
  if (entry.tag === "start") {
    return (
      <span className={`capsule capsule--start capsule--start-${entry.kind}`}>
        {entry.kind}
      </span>
    );
  }
  if (entry.tag === "exit") {
    return <span className="capsule capsule--exit">exit</span>;
  }
  const row = atomToPred(entry.atom);
  return (
    <span
      className={`capsule capsule--pred capsule--${row.kind}`}
      title={`#${entry.atom.node_id} · ${formatPred(row)}`}
    >
      {formatPredChip(row)}
    </span>
  );
}

function TipScore({ score }: { score: SoftScore }) {
  const pct = Math.round(Math.max(0, Math.min(1, score.overall)) * 100);
  return (
    <span className="mono muted compare-tree-node__tip" title={`tipScore ${score.overall.toFixed(2)}`}>
      tip {pct}%
    </span>
  );
}

function TreeNodeView({ data }: NodeProps<TreeFlowNode>) {
  return (
    <div className="compare-tree-node" style={{ width: NODE_W, minHeight: NODE_H }}>
      <Handle id="t" type="target" position={Position.Top} style={{ opacity: 0 }} />
      <div className="compare-tree-node__head">
        <span className={`compare-tree-node__badge compare-tree-node__badge--${data.start}`}>
          {data.start}
        </span>
        {data.tipScore ? <TipScore score={data.tipScore} /> : null}
      </div>
      <div className="compare-tree-node__cols">
        <div className="compare-tree-node__col">
          <span className="mono muted compare-tree-node__side">L</span>
          <div className="compare-tree-node__chips">
            {data.left.map((e, i) => (
              <EntryChip key={`l-${i}`} entry={e} />
            ))}
          </div>
        </div>
        <div className="compare-tree-node__col">
          <span className="mono muted compare-tree-node__side">R</span>
          <div className="compare-tree-node__chips">
            {data.right.map((e, i) => (
              <EntryChip key={`r-${i}`} entry={e} />
            ))}
          </div>
        </div>
      </div>
      <Handle id="b" type="source" position={Position.Bottom} style={{ opacity: 0 }} />
    </div>
  );
}

const nodeTypes = { tree: TreeNodeView };

type Props = {
  report: TreeReport;
};

export function CompareTreeView({ report }: Props) {
  const positions = useMemo(
    () => layoutTree(report.nodes, report.edges),
    [report.nodes, report.edges],
  );

  const onInit = useCallback((instance: ReactFlowInstance<TreeFlowNode, Edge>) => {
    void instance.fitView({ padding: 0.28, duration: 240 });
  }, []);

  const flowNodes = useMemo<TreeFlowNode[]>(() => {
    const out: TreeFlowNode[] = [];
    for (const n of report.nodes) {
      const id = String(n.id);
      const pos = positions[id];
      if (!pos) continue;
      out.push({
        id,
        type: "tree",
        position: { x: pos.x, y: pos.y },
        data: {
          start: n.start,
          left: n.left,
          right: n.right,
          tipScore: n.tipScore,
        },
        draggable: false,
      });
    }
    return out;
  }, [positions, report.nodes]);

  const flowEdges = useMemo<Edge[]>(() => {
    const placed = new Set(flowNodes.map((n) => n.id));
    return report.edges
      .filter((e) => placed.has(String(e.from)) && placed.has(String(e.to)))
      .map((e) => ({
        id: `${e.from}->${e.to}:${e.dir}`,
        source: String(e.from),
        target: String(e.to),
        sourceHandle: "b",
        targetHandle: "t",
        label: e.dir,
        className: "flow-edge flow-edge--branch",
        labelStyle: { fill: "#c9bfb0", fontSize: 10 },
      }));
  }, [flowNodes, report.edges]);

  return (
    <Flex className="compare-tree panel" flex="1" flexDirection="column" minHeight={0} minWidth={0}>
      <Box className="compare-tree__header" px={14} pt={12} pb={10}>
        <Text className="compare-tree__title" display="block">
          claim={report.claim} · behavioralEquivalence={report.behavioralEquivalence} · phase=
          {report.phase}
        </Text>
        <Text className="mono muted" display="block" fontSize={12} style={{ marginTop: 4 }}>
          {report.left.arch} expand {report.left.expandNodes} / seg {report.left.segments} ·{" "}
          {report.right.arch} expand {report.right.expandNodes} / seg {report.right.segments} · nodes{" "}
          {report.nodes.length} · forks {report.edges.length}
        </Text>
        <Text className="muted" display="block" fontSize={11} style={{ marginTop: 6 }}>
          {report.note}. Term equality is not proven.
        </Text>
      </Box>
      <Box className="compare-tree__canvas" flex="1" minHeight={0} position="relative">
        <ReactFlow
          nodes={flowNodes}
          edges={flowEdges}
          nodeTypes={nodeTypes}
          onInit={onInit}
          nodesDraggable={false}
          nodesFocusable={false}
          elementsSelectable={false}
          connectionMode={ConnectionMode.Loose}
          fitView={false}
          minZoom={0.15}
          maxZoom={2}
          proOptions={{ hideAttribution: false }}
          colorMode="dark"
        >
          <Background color="rgba(120,112,98,0.35)" gap={24} />
        </ReactFlow>
      </Box>
    </Flex>
  );
}
