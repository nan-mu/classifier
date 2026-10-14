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
import { matchStatusOf, type MatchStatus } from "./compareNodeSummary";
import { layoutCompareTree } from "./compareTreeLayout";
import { formatPredChip } from "./formatExpr";
import {
  atomToPred,
  type ListEntry,
  type StartKind,
  type TreeReport,
} from "./types";
import { formatPred } from "./viewer";

const MATCH_LEGEND = [
  { status: "pass", label: "谓词一致" },
  { status: "fail", label: "谓词不一致" },
] as const;

const NODE_W = 300;
const NODE_H = 132;
const PREVIEW_MAX = 3;
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
  match: MatchStatus;
  selected: boolean;
  onSelect: (id: number) => void;
};

type TreeFlowNode = Node<TreeFlowData, "tree">;

function EntryChip({ entry }: { entry: ListEntry }) {
  if (entry.tag === "start") {
    return <span className="capsule capsule--meta">{entry.kind}</span>;
  }
  if (entry.tag === "exit") {
    return <span className="capsule capsule--meta">exit</span>;
  }
  const row = atomToPred(entry.atom);
  return (
    <span className="capsule" title={formatPred(row)}>
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

const handleStyle = { opacity: 0, width: 8, height: 8 };

function TreeNodeView({ data }: NodeProps<TreeFlowNode>) {
  return (
    <div
      className={`state-node compare-tree-node compare-tree-node--${data.match}${
        data.selected ? " compare-tree-node--selected" : ""
      }`}
      style={{ width: NODE_W, height: NODE_H }}
    >
      <Handle id="l" type="target" position={Position.Left} style={handleStyle} />
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
    () => layoutCompareTree(report.nodes, report.edges),
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
          match: matchStatusOf(n),
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
        type: "smoothstep",
        pathOptions: { borderRadius: 12, offset: 0 },
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
        <div className="node-legend" aria-label="谓词比较图例">
          {MATCH_LEGEND.map((row) => (
            <div key={row.status} className="node-legend__row">
              <span className={`node-legend__swatch compare-tree-node--${row.status}`} />
              <span>{row.label}</span>
            </div>
          ))}
        </div>
      </Box>
    </Flex>
  );
}
