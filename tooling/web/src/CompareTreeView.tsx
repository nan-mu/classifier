import { Box, Flex } from "@kuma-ui/core";
import {
  Background,
  ConnectionMode,
  Handle,
  Position,
  ReactFlow,
  type Edge,
  type Node,
  type NodeMouseHandler,
  type NodeProps,
  type ReactFlowInstance,
} from "@xyflow/react";
import { useCallback, useEffect, useMemo, useRef } from "react";
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

const NODE_W = 300;
const NODE_H = 132;
const PREVIEW_MAX = 3;
/** Column stride: wide enough that dual-list cards stay readable at mid zoom. */
const GAP_X = 380;
/** Row stride matches fixed NODE_H + gutter so siblings never overlap. */
const GAP_Y = 168;
const BARY_PASSES = 8;
/** Above this, fitView hits minZoom and cards become unreadable — frame the root instead. */
const FIT_ALL_MAX_NODES = 24;
const ROOT_FRAME_ZOOM = 0.55;

type TreeFlowData = {
  id: number;
  start: StartKind;
  left: ListEntry[];
  right: ListEntry[];
  leftArch: string;
  rightArch: string;
  tipScore?: SoftScore;
  selected: boolean;
  onSelect: (id: number) => void;
};

type TreeFlowNode = Node<TreeFlowData, "tree">;

function startRole(start: StartKind): string {
  if (start === "taken") return "arm_taken";
  if (start === "not_taken") return "arm_not_taken";
  return "entry";
}

function bary(neighbors: string[], order: Map<string, number>): number {
  if (neighbors.length === 0) return Number.POSITIVE_INFINITY;
  let sum = 0;
  let n = 0;
  for (const id of neighbors) {
    const i = order.get(id);
    if (i === undefined) continue;
    sum += i;
    n += 1;
  }
  return n === 0 ? Number.POSITIVE_INFINITY : sum / n;
}

function layoutTree(
  nodes: TreeNode[],
  edges: TreeReport["edges"],
): Record<string, { x: number; y: number }> {
  if (nodes.length === 0) return {};
  const ids = nodes.map((n) => String(n.id));
  const idSet = new Set(ids);
  const children = new Map<string, string[]>();
  const parents = new Map<string, string[]>();
  const indeg = new Map<string, number>();
  const edgeDir = new Map<string, string>();

  for (const id of ids) {
    children.set(id, []);
    parents.set(id, []);
    indeg.set(id, 0);
  }
  for (const e of edges) {
    const from = String(e.from);
    const to = String(e.to);
    if (!idSet.has(from) || !idSet.has(to) || from === to) continue;
    children.get(from)!.push(to);
    parents.get(to)!.push(from);
    indeg.set(to, (indeg.get(to) ?? 0) + 1);
    edgeDir.set(`${from}->${to}`, e.dir);
  }
  for (const id of ids) {
    children.get(id)!.sort((a, b) => {
      const ra = edgeDir.get(`${id}->${a}`) === "taken" ? 0 : 1;
      const rb = edgeDir.get(`${id}->${b}`) === "taken" ? 0 : 1;
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

  const maxDepth = Math.max(0, ...depth.values());
  const layers: string[][] = Array.from({ length: maxDepth + 1 }, () => []);
  for (const id of ids) {
    layers[depth.get(id) ?? 0]!.push(id);
  }
  for (const layer of layers) {
    layer.sort((a, b) => Number(a) - Number(b));
  }

  for (let pass = 0; pass < BARY_PASSES; pass++) {
    for (let d = 1; d <= maxDepth; d++) {
      const layer = layers[d]!;
      const prev = layers[d - 1]!;
      const order = new Map(prev.map((id, i) => [id, i]));
      layer.sort((a, b) => {
        const ba = bary(parents.get(a) ?? [], order);
        const bb = bary(parents.get(b) ?? [], order);
        return ba - bb || Number(a) - Number(b);
      });
    }
    for (let d = maxDepth - 1; d >= 0; d--) {
      const layer = layers[d]!;
      const next = layers[d + 1]!;
      const order = new Map(next.map((id, i) => [id, i]));
      layer.sort((a, b) => {
        const ba = bary(children.get(a) ?? [], order);
        const bb = bary(children.get(b) ?? [], order);
        return ba - bb || Number(a) - Number(b);
      });
    }
  }

  const out: Record<string, { x: number; y: number }> = {};
  for (let d = 0; d <= maxDepth; d++) {
    const row = layers[d] ?? [];
    const totalH = Math.max(0, row.length - 1) * GAP_Y;
    const y0 = -totalH / 2;
    row.forEach((id, i) => {
      out[id] = { x: d * GAP_X, y: y0 + i * GAP_Y };
    });
  }
  return out;
}

function EntryChip({ entry }: { entry: ListEntry }) {
  if (entry.tag === "start") {
    return <span className="capsule capsule--meta">{entry.kind}</span>;
  }
  if (entry.tag === "exit") {
    return <span className="capsule capsule--meta">exit</span>;
  }
  const row = atomToPred(entry.atom);
  return (
    <span className="capsule" title={`#${entry.atom.node_id} · ${formatPred(row)}`}>
      {formatPredChip(row)}
    </span>
  );
}

function PreviewCol({
  label,
  entries,
}: {
  label: string;
  entries: ListEntry[];
}) {
  const shown = entries.slice(0, PREVIEW_MAX);
  const overflow = entries.length - shown.length;
  return (
    <div className="compare-tree-node__col">
      <span className="mono muted compare-tree-node__side">{label}</span>
      <div className="compare-tree-node__chips">
        {shown.map((e, i) => (
          <EntryChip key={`${label}-${i}`} entry={e} />
        ))}
        {overflow > 0 ? (
          <span className="mono muted compare-tree-node__more">+{overflow}</span>
        ) : null}
      </div>
    </div>
  );
}

function TipScore({ score }: { score: SoftScore }) {
  const pct = Math.round(Math.max(0, Math.min(1, score.overall)) * 100);
  return (
    <span
      className="mono muted state-node__meta"
      title={`分支末端启发式相似度 ${score.overall.toFixed(2)}`}
    >
      tip {pct}%
    </span>
  );
}

const handleStyle = { opacity: 0, width: 8, height: 8 };

function TreeNodeView({ data }: NodeProps<TreeFlowNode>) {
  const role = startRole(data.start);
  return (
    <div
      className={`state-node state-node--role-${role} compare-tree-node${
        data.selected ? " compare-tree-node--selected" : ""
      }`}
      style={{ width: NODE_W, height: NODE_H }}
    >
      <Handle id="l" type="target" position={Position.Left} style={handleStyle} />
      <div className="state-node__header">
        {data.tipScore ? <TipScore score={data.tipScore} /> : null}
      </div>
      <button
        type="button"
        className="state-node__title compare-tree-node__select"
        aria-pressed={data.selected}
        aria-label={`节点 ${data.id} ${data.start}`}
        onClick={(ev) => {
          ev.stopPropagation();
          data.onSelect(data.id);
        }}
        onKeyDown={(ev) => {
          if (ev.key === "Enter" || ev.key === " ") {
            ev.preventDefault();
            ev.stopPropagation();
            data.onSelect(data.id);
          }
        }}
      >
        #{data.id}
        <span className="state-node__loc"> · {data.start}</span>
      </button>
      <div className="compare-tree-node__cols">
        <PreviewCol label={`L · ${data.leftArch}`} entries={data.left} />
        <PreviewCol label={`R · ${data.rightArch}`} entries={data.right} />
      </div>
      <Handle id="r" type="source" position={Position.Right} style={handleStyle} />
    </div>
  );
}

const nodeTypes = { tree: TreeNodeView };

type Props = {
  report: TreeReport;
  selectedId: number | null;
  onSelectNode: (id: number) => void;
  leftArch: string;
  rightArch: string;
  fitRequest?: number;
};

export function CompareTreeView({
  report,
  selectedId,
  onSelectNode,
  leftArch,
  rightArch,
  fitRequest = 0,
}: Props) {
  const positions = useMemo(
    () => layoutTree(report.nodes, report.edges),
    [report.nodes, report.edges],
  );
  const flowRef = useRef<ReactFlowInstance<TreeFlowNode, Edge> | null>(null);
  const selectRef = useRef(onSelectNode);
  selectRef.current = onSelectNode;

  const onSelectStable = useCallback((id: number) => {
    selectRef.current(id);
  }, []);

  // Structure only — selectedId must not rebuild this (would reframe via effect).
  const structureNodes = useMemo<TreeFlowNode[]>(() => {
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
          id: n.id,
          start: n.start,
          left: n.left,
          right: n.right,
          leftArch,
          rightArch,
          tipScore: n.tipScore,
          selected: false,
          onSelect: onSelectStable,
        },
        draggable: false,
      });
    }
    return out;
  }, [positions, report.nodes, leftArch, rightArch, onSelectStable]);

  const flowNodes = useMemo<TreeFlowNode[]>(
    () =>
      structureNodes.map((n) => ({
        ...n,
        data: { ...n.data, selected: selectedId === n.data.id },
      })),
    [structureNodes, selectedId],
  );

  const flowEdges = useMemo<Edge[]>(() => {
    const placed = new Set(structureNodes.map((n) => n.id));
    return report.edges
      .filter((e) => placed.has(String(e.from)) && placed.has(String(e.to)))
      .map((e) => ({
        id: `${e.from}->${e.to}:${e.dir}`,
        source: String(e.from),
        target: String(e.to),
        sourceHandle: "r",
        targetHandle: "l",
        label: e.dir,
        className: "flow-edge flow-edge--branch",
        labelStyle: { fill: "#c9bfb0", fontSize: 10 },
      }));
  }, [structureNodes, report.edges]);

  const frameCamera = useCallback(
    (instance: ReactFlowInstance<TreeFlowNode, Edge>) => {
      const nodes = structureNodes;
      if (nodes.length === 0) return;
      if (nodes.length <= FIT_ALL_MAX_NODES) {
        void instance.fitView({ padding: 0.28, duration: 240 });
        return;
      }
      const root =
        nodes.find((n) => n.data.start === "create") ??
        [...nodes].sort(
          (a, b) => a.position.x - b.position.x || a.position.y - b.position.y,
        )[0]!;
      const zoom = ROOT_FRAME_ZOOM;
      const pane = document.querySelector(
        ".compare-tree__canvas .react-flow",
      ) as HTMLElement | null;
      const pw = pane?.clientWidth ?? 960;
      const ph = pane?.clientHeight ?? 640;
      const x = pw * 0.22 - root.position.x * zoom - (NODE_W * zoom) / 2;
      const y = ph * 0.5 - root.position.y * zoom - (NODE_H * zoom) / 2;
      void instance.setViewport({ x, y, zoom }, { duration: 240 });
    },
    [structureNodes],
  );

  const onInit = useCallback(
    (instance: ReactFlowInstance<TreeFlowNode, Edge>) => {
      flowRef.current = instance;
      frameCamera(instance);
    },
    [frameCamera],
  );

  useEffect(() => {
    const instance = flowRef.current;
    if (!instance) return;
    const id = requestAnimationFrame(() => frameCamera(instance));
    return () => cancelAnimationFrame(id);
  }, [frameCamera, structureNodes.length, report.phase]);

  useEffect(() => {
    if (fitRequest <= 0) return;
    const instance = flowRef.current;
    if (!instance) return;
    frameCamera(instance);
  }, [fitRequest, frameCamera]);

  const onNodeClick = useCallback<NodeMouseHandler>(
    (_event, node) => {
      onSelectNode(Number(node.id));
    },
    [onSelectNode],
  );

  if (report.nodes.length === 0) {
    return (
      <Flex
        className="compare-tree panel panel--canvas"
        flex="1"
        alignItems="center"
        justifyContent="center"
        minHeight={0}
        minWidth={0}
      >
        <Box className="mono muted">没有可比较节点</Box>
      </Flex>
    );
  }

  return (
    <Flex className="compare-tree panel panel--canvas" flex="1" flexDirection="column" minHeight={0} minWidth={0}>
      <Box className="compare-tree__canvas" flex="1" minHeight={0} position="relative">
        <ReactFlow
          nodes={flowNodes}
          edges={flowEdges}
          nodeTypes={nodeTypes}
          onInit={onInit}
          onNodeClick={onNodeClick}
          nodesDraggable={false}
          nodesFocusable={false}
          elementsSelectable={false}
          connectionMode={ConnectionMode.Loose}
          fitView={false}
          minZoom={0.12}
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
