import { Box, Button, Flex, Text } from "@kuma-ui/core";
import {
  Background,
  ConnectionMode,
  ReactFlow,
  ReactFlowProvider,
  useReactFlow,
  type Edge,
  type EdgeMouseHandler,
  type NodeMouseHandler,
} from "@xyflow/react";
import {
  useCallback,
  useEffect,
  useMemo,
  useRef,
  useState,
  type ChangeEvent,
  type ReactNode,
} from "react";
import "@xyflow/react/dist/style.css";
import { createSession, runSessionStream, stepSession } from "./api";
import { insnIndexForNode, localExprs, splitExprs } from "./exprs";
import { formatExprMath, formatPredChip } from "./formatExpr";
import { foldSameTypeChains, resolveFoldedId } from "./collapse";
import {
  classifyNodeRole,
  insnMnemonic,
  insnTextForNode,
  NODE_ROLE_LEGEND,
} from "./nodeRole";
import { StateNodeView, type StateFlowNode } from "./StateNode";
import type { ArchKind, ExprRow, PredRow, SessionSnapshot } from "./types";
import { useForceLayout } from "./useForceLayout";
import {
  branchSource,
  countBranchEdges,
  diffExprs,
  diffPredicates,
  edgeKey,
  inboundEdges,
  outboundEdges,
  parseEdgeKey,
  pathToRoot,
  processedIds,
  visibleNodeIds,
  type ViewerSelection,
} from "./viewer";

const nodeTypes = { state: StateNodeView };
const EMPTY_FLOW_NODES: StateFlowNode[] = [];
const EMPTY_FLOW_EDGES: Edge[] = [];

const statusLabel: Record<SessionSnapshot["status"], string> = {
  running: "进行中",
  complete: "完成",
  fail: "未完成",
};

function ExprCapsules({ exprs }: { exprs: ExprRow[] }) {
  if (exprs.length === 0) {
    return <Text className="mono muted capsule-empty">∅</Text>;
  }
  return (
    <div className="capsule-row">
      {exprs.map((e, i) => (
        <span
          key={`${e.reg}-${e.rel}-${i}`}
          className={`capsule${e.role === "constraint" ? " capsule--constraint" : ""}`}
          title={`${e.reg} ${e.rel} ${e.term}`}
        >
          {formatExprMath(e)}
        </span>
      ))}
    </div>
  );
}

function PredCapsules({ preds }: { preds: PredRow[] }) {
  if (preds.length === 0) {
    return <Text className="mono muted capsule-empty">∅</Text>;
  }
  return (
    <div className="capsule-row">
      {preds.map((p, i) => (
        <span
          key={i}
          className={`capsule capsule--pred capsule--${p.kind}`}
          title={formatPredChip(p)}
        >
          {formatPredChip(p)}
        </span>
      ))}
    </div>
  );
}

function SemBlock({ tag, children }: { tag: ReactNode; children: ReactNode }) {
  return (
    <div className="sem-block">
      <span className="sem-tag mono">{tag}</span>
      <div className="sem-block__body">{children}</div>
    </div>
  );
}

function EgTag() {
  return (
    <>
      E<sub>g</sub>
    </>
  );
}

function EiTag({ on }: { on?: "taken" | "not_taken" | "only" }) {
  if (on === "taken") {
    return (
      <>
        E<sub>i</sub> on taken
      </>
    );
  }
  if (on === "not_taken") {
    return (
      <>
        E<sub>i</sub> on not taken
      </>
    );
  }
  if (on === "only") {
    return (
      <>
        E<sub>i</sub>
      </>
    );
  }
  return (
    <>
      E<sub>i</sub>
    </>
  );
}

function PgTag() {
  return (
    <>
      P<sub>g</sub>
    </>
  );
}

function eiOnLabel(dir: string | null | undefined): "taken" | "not_taken" | "only" {
  if (dir === "taken") return "taken";
  if (dir === "not_taken") return "not_taken";
  return "only";
}

export function App() {
  return (
    <ReactFlowProvider>
      <DebugScreen />
    </ReactFlowProvider>
  );
}

function DebugScreen() {
  const [snap, setSnap] = useState<SessionSnapshot | null>(null);
  const [sel, setSel] = useState<ViewerSelection>({
    focus: 0,
    compare: null,
    edgeKey: null,
    collapseSameLoc: false,
    panel: "node",
  });
  const [budget, setBudget] = useState(1024);
  const [arch, setArch] = useState<ArchKind>("rv32imc");
  const [firmwareName, setFirmwareName] = useState("just_tx.elf");
  const [firmwareBytes, setFirmwareBytes] = useState<ArrayBuffer | null>(null);
  const [busy, setBusy] = useState(false);
  const [streaming, setStreaming] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [runRate, setRunRate] = useState<string | null>(null);
  const insnRef = useRef<HTMLDivElement | null>(null);
  const logRef = useRef<HTMLDivElement | null>(null);
  const fileRef = useRef<HTMLInputElement | null>(null);
  const runAbortRef = useRef<AbortController | null>(null);
  const pendingSnapRef = useRef<SessionSnapshot | null>(null);
  const rafRef = useRef<number | null>(null);
  const fitOnceRef = useRef(true);
  const flow = useReactFlow();

  const flushPendingSnap = useCallback(() => {
    rafRef.current = null;
    const next = pendingSnapRef.current;
    if (!next) return;
    pendingSnapRef.current = null;
    setSnap(next);
    setSel((s) => ({ ...s, focus: next.focus, edgeKey: null }));
  }, []);

  const apply = useCallback(
    (next: SessionSnapshot, opts?: { immediate?: boolean }) => {
      if (opts?.immediate) {
        pendingSnapRef.current = null;
        if (rafRef.current != null) {
          cancelAnimationFrame(rafRef.current);
          rafRef.current = null;
        }
        setSnap(next);
        setSel((s) => ({ ...s, focus: next.focus, edgeKey: null }));
        return;
      }
      pendingSnapRef.current = next;
      if (rafRef.current == null) {
        rafRef.current = requestAnimationFrame(flushPendingSnap);
      }
    },
    [flushPendingSnap],
  );

  const boot = useCallback(
    async (nextArch: ArchKind, b: number, name: string, image: ArrayBuffer | null) => {
      runAbortRef.current?.abort();
      runAbortRef.current = null;
      setBusy(true);
      setStreaming(false);
      setError(null);
      setRunRate(null);
      fitOnceRef.current = true;
      try {
        const next = await createSession({
          budget: b,
          arch: nextArch,
          name,
          image,
        });
        apply(next, { immediate: true });
        setSel((s) => ({
          ...s,
          focus: next.focus,
          compare: null,
          edgeKey: null,
        }));
      } catch (err: unknown) {
        setError(err instanceof Error ? err.message : "session failed");
      } finally {
        setBusy(false);
      }
    },
    [apply],
  );

  useEffect(() => {
    void boot("rv32imc", 1024, "just_tx.elf", null);
  }, [boot]);

  const onFirmwarePick = useCallback((ev: ChangeEvent<HTMLInputElement>) => {
    const file = ev.target.files?.[0];
    if (!file) {
      setFirmwareName("just_tx.elf");
      setFirmwareBytes(null);
      return;
    }
    void file.arrayBuffer().then((buf) => {
      setFirmwareName(file.name);
      setFirmwareBytes(buf);
    });
  }, []);

  const focusedNode = snap?.nodes.find((n) => n.id === sel.focus) ?? null;
  const compareNode =
    sel.compare === null ? null : (snap?.nodes.find((n) => n.id === sel.compare) ?? null);
  const highlightJ = useMemo(
    () => (snap ? insnIndexForNode(focusedNode, snap.nodes) : null),
    [focusedNode, snap],
  );

  useEffect(() => {
    if (streaming) return;
    insnRef.current?.scrollIntoView({ block: "center", behavior: "smooth" });
  }, [highlightJ, snap?.insns.length, streaming]);

  useEffect(() => {
    if (streaming) return;
    logRef.current?.scrollIntoView({ block: "end" });
  }, [snap?.log.length, streaming]);

  const visible = useMemo(() => {
    if (!snap) return new Set<number>();
    return visibleNodeIds(snap, sel.focus, sel.compare, sel.collapseSameLoc);
  }, [snap, sel.focus, sel.compare, sel.collapseSameLoc]);

  const nodeTypeById = useMemo(() => {
    const map = new Map<number, string>();
    if (!snap) return map;
    const failedId = snap.status === "fail" ? snap.failed : null;
    for (const node of snap.nodes) {
      const info = classifyNodeRole({
        node,
        edges: snap.edges,
        insnText: insnTextForNode(node, snap.insns),
        work: snap.work,
        failedId,
      });
      map.set(node.id, info.nodeType);
    }
    return map;
  }, [snap]);

  const typeFold = useMemo(() => {
    if (!snap) {
      return foldSameTypeChains([], [], () => "", new Set());
    }
    // Only pin the nodes the user is looking at — protecting the whole
    // path-to-root used to disable same-type folding on the main spine.
    const protectedIds = new Set<number>([sel.focus, ...snap.work]);
    if (sel.compare != null) protectedIds.add(sel.compare);
    if (snap.status === "fail" && snap.failed != null) protectedIds.add(snap.failed);
    return foldSameTypeChains(
      snap.nodes.filter((n) => visible.has(n.id)),
      snap.edges.filter((e) => visible.has(e.from) && visible.has(e.to)),
      (id) => nodeTypeById.get(id) ?? "",
      protectedIds,
    );
  }, [snap, visible, sel.focus, sel.compare, nodeTypeById]);

  const displayNodes = useMemo(
    () =>
      snap
        ? snap.nodes.filter((n) => visible.has(n.id) && !typeFold.hidden.has(n.id))
        : [],
    [snap, visible, typeFold],
  );
  const displayNodeIds = useMemo(
    () => new Set(displayNodes.map((n) => n.id)),
    [displayNodes],
  );
  const displayEdges = useMemo(() => {
    if (!snap) return [];
    const seen = new Set<string>();
    const out: typeof snap.edges = [];
    for (const e of snap.edges) {
      if (!visible.has(e.from) || !visible.has(e.to)) continue;
      if (typeFold.hidden.has(e.from)) continue;
      const to = resolveFoldedId(e.to, typeFold);
      if (!displayNodeIds.has(e.from) || !displayNodeIds.has(to)) continue;
      if (e.from === to) continue;
      const key = `${e.from}->${to}:${e.dir}`;
      if (seen.has(key)) continue;
      seen.add(key);
      out.push(to === e.to ? e : { from: e.from, to, dir: e.dir });
    }
    return out;
  }, [snap, visible, typeFold, displayNodeIds]);

  // While running: cheap incremental placement. After complete/fail: final layout.
  const layoutMode =
    snap?.status === "complete" || snap?.status === "fail" ? "final" : "fast";
  const positions = useForceLayout(
    displayNodes,
    displayEdges,
    `${snap?.id ?? ""}:${layoutMode}`,
    layoutMode,
  );
  const hasPositions = Object.keys(positions).length > 0;

  const finalFitKeyRef = useRef("");
  useEffect(() => {
    // Never fit on focus/fold churn — that resets the camera on node clicks.
    if (streaming || !hasPositions) return;
    let doFit = false;
    if (fitOnceRef.current) {
      fitOnceRef.current = false;
      doFit = true;
    } else if (layoutMode === "final") {
      const k = `${snap?.id ?? ""}:final`;
      if (finalFitKeyRef.current !== k) {
        finalFitKeyRef.current = k;
        doFit = true;
      }
    }
    if (!doFit) return;
    const frame = requestAnimationFrame(() => {
      void flow.fitView({ padding: 0.28, duration: 240 });
    });
    return () => cancelAnimationFrame(frame);
  }, [flow, streaming, layoutMode, snap?.id, hasPositions]);

  const head = snap?.work[0];
  const canStep = Boolean(
    snap && snap.status === "running" && !busy && sel.focus === head,
  );
  const canRun = Boolean(snap && snap.status === "running" && !busy);
  const done = useMemo(() => (snap ? processedIds(snap) : new Set<number>()), [snap]);

  const focusedSplit = useMemo(() => {
    if (!focusedNode || !snap) return null;
    return splitExprs(focusedNode, snap.nodes, snap.edges);
  }, [focusedNode, snap]);

  const selectedEdge = useMemo(() => {
    if (!snap || !sel.edgeKey) return null;
    const parsed = parseEdgeKey(sel.edgeKey);
    if (!parsed) return null;
    return (
      snap.edges.find(
        (e) => e.from === parsed.from && e.to === parsed.to && e.dir === parsed.dir,
      ) ?? null
    );
  }, [sel.edgeKey, snap]);

  const pathIds = useMemo(
    () => (snap ? pathToRoot(sel.focus, snap.nodes) : []),
    [sel.focus, snap],
  );

  const onStep = useCallback(async () => {
    if (!snap || snap.status !== "running" || snap.work[0] !== sel.focus) return;
    setBusy(true);
    setError(null);
    try {
      apply(await stepSession(snap.id), { immediate: true });
    } catch (err: unknown) {
      setError(err instanceof Error ? err.message : "step failed");
    } finally {
      setBusy(false);
    }
  }, [apply, sel.focus, snap]);

  const onRun = useCallback(async () => {
    if (!snap || snap.status !== "running") return;
    runAbortRef.current?.abort();
    const ac = new AbortController();
    runAbortRef.current = ac;
    setBusy(true);
    setStreaming(true);
    setError(null);
    setRunRate(null);
    try {
      const final = await runSessionStream(
        snap.id,
        (next, stats) => {
          apply(next);
          setRunRate(
            `${stats.stepsPerSec.toFixed(1)} step/s  ${stats.steps} steps  ${(
              stats.elapsedMs / 1000
            ).toFixed(2)}s`,
          );
        },
        ac.signal,
      );
      apply(final, { immediate: true });
    } catch (err: unknown) {
      if (!ac.signal.aborted) {
        setError(err instanceof Error ? err.message : "run failed");
      }
      flushPendingSnap();
    } finally {
      if (runAbortRef.current === ac) runAbortRef.current = null;
      setStreaming(false);
      setBusy(false);
    }
  }, [apply, flushPendingSnap, snap]);

  const onNodeClick = useCallback<NodeMouseHandler>((event, node) => {
    const id = Number(node.id);
    if (event.shiftKey) {
      setSel((s) => ({
        ...s,
        compare: s.compare === id ? null : id,
        panel: "compare",
      }));
      return;
    }
    setSel((s) => ({ ...s, focus: id, edgeKey: null }));
  }, []);

  const onEdgeClick = useCallback<EdgeMouseHandler>((_event, edge) => {
    setSel((s) => ({
      ...s,
      edgeKey: edge.id,
      focus: Number(edge.source),
      panel: "step",
    }));
  }, []);

  const flowNodes = useMemo<StateFlowNode[]>(() => {
    if (!snap) return EMPTY_FLOW_NODES;
    const headId = snap.work[0];
    const failedId = snap.status === "fail" ? snap.failed : null;
    const out: StateFlowNode[] = [];
    for (const node of displayNodes) {
      const id = String(node.id);
      const pos = positions[id];
      if (!pos) continue;
      const insnText = insnTextForNode(node, snap.insns);
      const { role, tags, accessFamily } = classifyNodeRole({
        node,
        edges: snap.edges,
        insnText,
        work: snap.work,
        failedId,
      });
      const mnemonic = insnMnemonic(insnText);
      const folded = typeFold.foldedCount.get(node.id);
      out.push({
        id,
        type: "state",
        position: { x: pos.x, y: pos.y },
        data: {
          nodeId: node.id,
          loc: node.loc,
          egCount: node.exprs.length,
          predCount: node.predicates.length,
          focused: node.id === sel.focus,
          compare: node.id === sel.compare,
          head: node.id === headId,
          processed: done.has(node.id),
          role,
          tags,
          insnHint: mnemonic || undefined,
          foldedCount: folded,
          accessFamily,
        },
        draggable: false,
      });
    }
    return out.length === 0 ? EMPTY_FLOW_NODES : out;
  }, [done, displayNodes, typeFold, positions, sel.compare, sel.focus, snap]);

  const flowEdges = useMemo<Edge[]>(() => {
    if (!snap || flowNodes.length === 0) return EMPTY_FLOW_EDGES;
    const placed = new Set(flowNodes.map((n) => n.id));
    const next = displayEdges
      .filter((edge) => placed.has(String(edge.from)) && placed.has(String(edge.to)))
      .map((edge) => {
        const id = edgeKey(edge);
        const branch = edge.dir === "taken" || edge.dir === "not_taken";
        const reuse = edge.dir === "reuse";
        return {
          id,
          source: String(edge.from),
          target: String(edge.to),
          sourceHandle: "r",
          targetHandle: "l",
          type: reuse ? "straight" : "default",
          label: edge.dir === "only" ? undefined : edge.dir,
          className: `flow-edge${branch ? " flow-edge--branch" : ""}${reuse ? " flow-edge--reuse" : ""}${
            sel.edgeKey === id ? " flow-edge--sel" : ""
          }`,
          labelStyle: { fill: "#c9bfb0", fontSize: 10 },
        };
      });
    return next.length === 0 ? EMPTY_FLOW_EDGES : next;
  }, [flowNodes, displayEdges, sel.edgeKey, snap]);

  const dualTakenNotTaken = useMemo(() => {
    if (!snap || !focusedNode) return null;
    const outs = outboundEdges(focusedNode.id, snap.edges);
    const taken = outs.filter((e) => e.dir === "taken");
    const notTaken = outs.filter((e) => e.dir === "not_taken");
    if (taken.length === 0 && notTaken.length === 0) return null;
    return { taken, notTaken };
  }, [focusedNode, snap]);

  const branchStats = useMemo(
    () => (snap ? countBranchEdges(snap) : { taken: 0, notTaken: 0 }),
    [snap],
  );

  const focusBranchSource = useCallback(() => {
    if (!snap) return;
    const src = branchSource(sel.focus, snap.edges);
    if (src === null) return;
    setSel((s) => ({ ...s, focus: src, panel: "node", edgeKey: null }));
  }, [sel.focus, snap]);

  return (
    <Flex className="app-shell" height="100%" flexDirection="column">
      <Flex className="topbar" alignItems="center" gap={10} px={12} pt={10}>
        <Text className="panel__title" p={0}>
          架构
        </Text>
        <select
          className="toolbar__select"
          value={arch}
          disabled={busy}
          onChange={(ev) => setArch(ev.target.value as ArchKind)}
        >
          <option value="rv32imc">RV32IMC</option>
        </select>
        <Text className="muted">XDP ELF</Text>
        <label className="toolbar__file">
          <input
            ref={fileRef}
            type="file"
            accept=".elf"
            disabled={busy}
            onChange={onFirmwarePick}
          />
          <span className="toolbar__file-btn">选择文件</span>
        </label>
        <Text className="mono muted" fontSize={11} title={firmwareName}>
          {firmwareBytes ? firmwareName : "just_tx.elf（默认）"}
        </Text>
        {firmwareBytes ? (
          <Button
            type="button"
            className="toolbar__btn toolbar__btn--quiet"
            disabled={busy}
            onClick={() => {
              setFirmwareName("just_tx.elf");
              setFirmwareBytes(null);
              if (fileRef.current) fileRef.current.value = "";
            }}
          >
            恢复默认
          </Button>
        ) : null}
        <Text className="muted">budget</Text>
        <input
          className="toolbar__input mono"
          type="number"
          min={0}
          max={2048}
          value={budget}
          disabled={busy}
          onChange={(ev) => setBudget(Number(ev.target.value) || 0)}
        />
        <Button
          type="button"
          className="toolbar__btn"
          disabled={busy}
          onClick={() => void boot(arch, budget, firmwareName, firmwareBytes)}
        >
          新建运行
        </Button>
        <Text className="mono muted" fontSize={11}>
          快照不可变 · Shift+点击设比较 · 同类型自动折叠 · {snap?.proof_note ?? ""}
        </Text>
      </Flex>

      <Flex flex="1" minHeight={0} gap={12} p={12} pt={8}>
        <Flex className="panel panel--left" width={300} flexDirection="column" minHeight={0}>
          <Text className="panel__title">指令 / 位置</Text>
          <Box className="panel__body insn-list" flex="1" overflow="auto" minHeight={0}>
            {snap?.insns.map((insn) => {
              const current = highlightJ === insn.j;
              const exec = snap.cursor_j === insn.j;
              const sp = insn.text.indexOf(" ");
              const addr = sp < 0 ? insn.text : insn.text.slice(0, sp);
              const body = sp < 0 ? "" : insn.text.slice(sp + 1);
              return (
                <Box
                  key={insn.j}
                  ref={current ? insnRef : undefined}
                  className={`insn-row${current ? " insn-row--focus" : ""}${
                    exec ? " insn-row--exec" : ""
                  }`}
                >
                  <span className="insn-row__addr mono">{addr}</span>
                  <span className="insn-row__body mono">{body}</span>
                </Box>
              );
            })}
          </Box>
          <Box className="meta-strip" px={12} py={8}>
            <Text className="mono muted" display="block" fontSize={11}>
              Work [{snap?.work.join(", ") ?? ""}] · fuel {snap?.fuel ?? "—"}/
              {snap?.budget ?? "—"}
            </Text>
            <Text className="mono muted" display="block" fontSize={11}>
              已处理 {done.size} · 节点 {snap?.nodes.length ?? 0} · 边{" "}
              {snap?.edges.length ?? 0}
            </Text>
            {branchStats.taken > 0 || branchStats.notTaken > 0 ? (
              <button
                type="button"
                className="branch-chip"
                onClick={focusBranchSource}
              >
                分支 Taken×{branchStats.taken} / NotTaken×{branchStats.notTaken}
                （点此跳到分支源）
              </button>
            ) : null}
            {snap?.status === "fail" ? (
              <Text className="fail-banner" display="block">
                未完成 · {snap.reason ?? "?"}（保留部分图）
                {snap.failed != null ? ` · 拒绝节点 #${snap.failed}` : ""}
              </Text>
            ) : null}
          </Box>
        </Flex>

        <Box className="panel panel--canvas" flex="1" minWidth={0} position="relative">
          {error ? (
            <Text className="error-banner" p={16} fontSize={13}>
              {error}
            </Text>
          ) : null}
          <ReactFlow
            nodes={flowNodes}
            edges={flowEdges}
            nodeTypes={nodeTypes}
            onNodeClick={onNodeClick}
            onEdgeClick={onEdgeClick}
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
          {snap && flowNodes.length > 0 ? (
            <div className="node-legend" aria-label="节点类型图例">
              {NODE_ROLE_LEGEND.map((row) => (
                <div key={row.role} className="node-legend__row">
                  <span
                    className={`node-legend__swatch state-node--role-${row.role}${
                      row.role.startsWith("reg_") ? " state-node--access" : ""
                    }`}
                  />
                  <span>{row.label}</span>
                </div>
              ))}
            </div>
          ) : null}
          <div className="canvas-float" aria-label="运行控制">
            <button
              type="button"
              className="canvas-float__btn"
              onClick={() => void onStep()}
              disabled={!canStep}
            >
              单步（Work 首）
            </button>
            <button
              type="button"
              className="canvas-float__btn"
              onClick={() => void onRun()}
              disabled={!canRun}
            >
              运行到结束
            </button>
            <span className="mono canvas-float__status">
              {snap
                ? `${statusLabel[snap.status]}  fuel ${snap.fuel}/${snap.budget}  ${
                    snap.arch
                  }  ${snap.program}${snap.reason ? `  ${snap.reason}` : ""}${
                    runRate ? `  ${runRate}` : ""
                  }`
                : "连接中"}
            </span>
          </div>
        </Box>

        <Flex className="panel panel--right" flexDirection="column" minHeight={0}>
          <Flex className="panel-tabs" gap={6} px={10} pt={8}>
            {(
              [
                ["node", "节点"],
                ["step", "边"],
                ["path", "路径"],
                ["compare", "比较"],
              ] as const
            ).map(([id, label]) => (
              <button
                key={id}
                type="button"
                className={`tab-btn${sel.panel === id ? " tab-btn--on" : ""}`}
                onClick={() => setSel((s) => ({ ...s, panel: id }))}
              >
                {label}
              </button>
            ))}
          </Flex>

          <Box className="panel__body panel__body--state" flex="1" overflow="auto" minHeight={0} px={12} pb={8}>
            {sel.panel === "node" && focusedNode && focusedSplit ? (
              <>
                <Text className="sem-heading">
                  #{focusedNode.id}
                  {focusedNode.loc === "exit" ? " · exit" : ` · pos ${focusedNode.loc}`}
                </Text>
                <SemBlock tag={<EgTag />}>
                  <ExprCapsules exprs={focusedSplit.eg} />
                </SemBlock>
                {focusedSplit.eiIn.length > 0 ? (
                  <SemBlock tag={<EiTag />}>
                    <ExprCapsules exprs={focusedSplit.eiIn} />
                  </SemBlock>
                ) : null}
                {focusedSplit.eiOut
                  .filter((d) => d.exprs.length > 0)
                  .map((delta) => (
                    <SemBlock key={delta.to} tag={<EiTag on={eiOnLabel(delta.dir)} />}>
                      <ExprCapsules exprs={delta.exprs} />
                    </SemBlock>
                  ))}
                <SemBlock tag={<PgTag />}>
                  <PredCapsules preds={focusedNode.predicates} />
                </SemBlock>
                {dualTakenNotTaken ? (
                  <Text className="mono muted" display="block" fontSize={11}>
                    T→{dualTakenNotTaken.taken.map((e) => e.to).join(",") || "∅"}
                    {" · "}
                    N→{dualTakenNotTaken.notTaken.map((e) => e.to).join(",") || "∅"}
                  </Text>
                ) : null}
              </>
            ) : null}

            {sel.panel === "step" && snap ? (
              <>
                <Text className="sem-heading">边</Text>
                {selectedEdge ? (
                  <>
                    <Text className="mono muted" display="block" fontSize={11}>
                      {selectedEdge.from} —{selectedEdge.dir}→ {selectedEdge.to}
                    </Text>
                    {(() => {
                      const src = snap.nodes.find((n) => n.id === selectedEdge.from);
                      const dst = snap.nodes.find((n) => n.id === selectedEdge.to);
                      if (!src || !dst) return null;
                      const delta = localExprs(src.exprs, dst.exprs);
                      return (
                        <>
                          <SemBlock tag={<EiTag on={eiOnLabel(selectedEdge.dir)} />}>
                            <ExprCapsules exprs={delta} />
                          </SemBlock>
                          <SemBlock tag={<PgTag />}>
                            <PredCapsules preds={dst.predicates} />
                          </SemBlock>
                        </>
                      );
                    })()}
                  </>
                ) : (
                  <Text className="muted">点击图上的边。</Text>
                )}
                {focusedNode
                  ? inboundEdges(focusedNode.id, snap.edges).map((e) => (
                      <Text key={edgeKey(e)} className="mono muted" display="block" fontSize={11}>
                        #{e.from} —{e.dir}→ #{e.to}
                      </Text>
                    ))
                  : null}
              </>
            ) : null}

            {sel.panel === "path" && snap ? (
              <>
                <Text className="sem-heading">路径</Text>
                <Text className="mono muted" display="block" fontSize={11}>
                  {pathIds.map((id) => `#${id}`).join(" → ")}
                </Text>
                {pathIds.map((id) => {
                  const n = snap.nodes.find((x) => x.id === id);
                  if (!n) return null;
                  return (
                    <SemBlock key={id} tag={`#${id}`}>
                      <PredCapsules preds={n.predicates} />
                    </SemBlock>
                  );
                })}
              </>
            ) : null}

            {sel.panel === "compare" ? (
              <>
                <Text className="sem-heading">比较</Text>
                <Text className="muted" display="block" fontSize={11}>
                  #{sel.focus}
                  {sel.compare !== null ? ` · #${sel.compare}` : " · Shift+点击第二节点"}
                </Text>
                {focusedNode && compareNode ? (
                  <>
                    <Text className="mono muted" display="block" fontSize={11}>
                      loc {focusedNode.loc === compareNode.loc ? "=" : "≠"}{" "}
                      {focusedNode.loc}/{compareNode.loc}
                    </Text>
                    {(() => {
                      const d = diffExprs(focusedNode.exprs, compareNode.exprs);
                      const pd = diffPredicates(
                        focusedNode.predicates,
                        compareNode.predicates,
                      );
                      return (
                        <>
                          {d.added.length > 0 ? (
                            <SemBlock tag="+E">
                              <ExprCapsules exprs={d.added} />
                            </SemBlock>
                          ) : null}
                          {d.removed.length > 0 ? (
                            <SemBlock tag="−E">
                              <ExprCapsules exprs={d.removed} />
                            </SemBlock>
                          ) : null}
                          {d.changed.length > 0 ? (
                            <SemBlock tag="ΔE">
                              <ExprCapsules exprs={d.changed.map((c) => c.after)} />
                            </SemBlock>
                          ) : null}
                          {pd.added.length > 0 ? (
                            <SemBlock tag="+P">
                              <PredCapsules preds={pd.added} />
                            </SemBlock>
                          ) : null}
                          {pd.removed.length > 0 ? (
                            <SemBlock tag="−P">
                              <PredCapsules preds={pd.removed} />
                            </SemBlock>
                          ) : null}
                        </>
                      );
                    })()}
                  </>
                ) : (
                  <Text className="muted">需要两个节点。</Text>
                )}
              </>
            ) : null}

            {!focusedNode ? <Text className="muted">等待节点…</Text> : null}
          </Box>

          <Box className="log-strip">
            <Text className="panel__title panel__title--small">日志</Text>
            <Box className="log-strip__body" maxHeight={120} overflow="auto" px={12} pb={10}>
              {snap?.log.map((entry) => (
                <Text key={entry.t} className="mono log-line" display="block">
                  {entry.t}. {entry.msg}
                </Text>
              ))}
              <Box ref={logRef} />
            </Box>
          </Box>
        </Flex>
      </Flex>

    </Flex>
  );
}
