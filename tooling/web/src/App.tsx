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
} from "react";
import "@xyflow/react/dist/style.css";
import { createSession, runSession, stepSession } from "./api";
import { insnIndexForNode, localExprs, splitExprs } from "./exprs";
import {
  formatRegLabel,
  groupExprsByKind,
  kindLabel,
  parseReg,
  parseTerm,
  termToPlain,
} from "./parse";
import { StateNodeView, type StateFlowNode } from "./StateNode";
import type { ArchKind, ExprRow, PredRow, SessionSnapshot } from "./types";
import { useForceLayout } from "./useForceLayout";
import {
  countBranchEdges,
  diffExprs,
  diffPredicates,
  edgeKey,
  formatPred,
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

function TermTree({ view, depth = 0 }: { view: ReturnType<typeof parseTerm>; depth?: number }) {
  const pad = { paddingLeft: depth * 10 };
  if (view.kind === "const") {
    return (
      <Text className="mono term-leaf" style={pad} display="block">
        const {view.digits}
      </Text>
    );
  }
  if (view.kind === "var") {
    return (
      <Text className="mono term-leaf" style={pad} display="block">
        var{view.width ?? "?"} : {view.name}
      </Text>
    );
  }
  if (view.kind === "app") {
    return (
      <Box style={pad}>
        <Text className="mono term-op" display="block">
          {view.op}(
        </Text>
        {view.args.map((arg, i) => (
          <TermTree key={i} view={arg} depth={depth + 1} />
        ))}
        <Text className="mono term-op" display="block">
          )
        </Text>
      </Box>
    );
  }
  const asReg = parseReg(view.text);
  if (asReg.kind !== "unknown") {
    return (
      <Text className="mono term-leaf" style={pad} display="block">
        {formatRegLabel(asReg)} · {view.text}
      </Text>
    );
  }
  return (
    <Text className="mono term-leaf" style={pad} display="block">
      {view.text}
    </Text>
  );
}

function ExprDetail({ e }: { e: ExprRow }) {
  const reg = parseReg(e.reg);
  const term = parseTerm(e.term);
  return (
    <Box className="expr-card">
      <Text className="mono sem-line" display="block">
        {formatRegLabel(reg)} · {e.rel}
      </Text>
      <Text className="mono muted" display="block" fontSize={11}>
        raw {e.reg} · view {termToPlain(term)}
      </Text>
      <TermTree view={term} />
    </Box>
  );
}

function ExprGroups({ exprs }: { exprs: ExprRow[] }) {
  if (exprs.length === 0) {
    return <Text className="mono muted">∅</Text>;
  }
  return (
    <>
      {groupExprsByKind(exprs).map(({ kind, rows }) => (
        <Box key={kind} className="expr-group">
          <Text className="expr-group__title mono" display="block">
            {kindLabel[kind]} · {rows.length}
          </Text>
          {rows.map((expr, index) => (
            <ExprDetail key={`${kind}-${expr.reg}-${index}`} e={expr} />
          ))}
        </Box>
      ))}
    </>
  );
}

function PredDetail({ p }: { p: PredRow }) {
  const kindClass =
    p.kind === "cmp"
      ? " pred-cmp"
      : p.kind === "ret"
        ? " pred-ret"
        : p.kind === "helper"
          ? " pred-helper"
          : "";
  return (
    <Box className={`pred-card${kindClass}`}>
      <Text className={`mono sem-line${kindClass}`} display="block">
        {formatPred(p)}
      </Text>
      {p.kind === "cmp" ? (
        <>
          <Text className="mono muted" display="block" fontSize={11}>
            lhs
          </Text>
          <TermTree view={parseTerm(p.lhs ?? "")} />
          <Text className="mono muted" display="block" fontSize={11}>
            rhs
          </Text>
          <TermTree view={parseTerm(p.rhs ?? "")} />
        </>
      ) : null}
      {p.kind === "ret" ? <TermTree view={parseTerm(p.term ?? "")} /> : null}
      {p.kind === "helper"
        ? (p.args ?? []).map((arg, i) => (
            <Box key={i}>
              <Text className="mono muted" display="block" fontSize={11}>
                arg{i}
              </Text>
              <TermTree view={parseTerm(arg)} />
            </Box>
          ))
        : null}
    </Box>
  );
}

function PredList({ preds }: { preds: PredRow[] }) {
  if (preds.length === 0) {
    return <Text className="mono muted">∅</Text>;
  }
  return (
    <>
      {preds.map((p, i) => (
        <PredDetail key={i} p={p} />
      ))}
    </>
  );
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
  const [budget, setBudget] = useState(512);
  const [arch, setArch] = useState<ArchKind>("rv32imc");
  const [firmwareName, setFirmwareName] = useState("just_tx.elf");
  const [firmwareBytes, setFirmwareBytes] = useState<ArrayBuffer | null>(null);
  const [busy, setBusy] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const insnRef = useRef<HTMLDivElement | null>(null);
  const logRef = useRef<HTMLDivElement | null>(null);
  const fileRef = useRef<HTMLInputElement | null>(null);
  const flow = useReactFlow();

  const boot = useCallback(
    async (nextArch: ArchKind, b: number, name: string, image: ArrayBuffer | null) => {
      setBusy(true);
      setError(null);
      try {
        const next = await createSession({
          budget: b,
          arch: nextArch,
          name,
          image,
        });
        setSnap(next);
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
    [],
  );

  useEffect(() => {
    void boot("rv32imc", 512, "just_tx.elf", null);
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
    insnRef.current?.scrollIntoView({ block: "center", behavior: "smooth" });
  }, [highlightJ, snap?.insns.length]);

  useEffect(() => {
    logRef.current?.scrollIntoView({ block: "end" });
  }, [snap?.log.length]);

  const visible = useMemo(() => {
    if (!snap) return new Set<number>();
    return visibleNodeIds(snap, sel.focus, sel.compare, sel.collapseSameLoc);
  }, [snap, sel.focus, sel.compare, sel.collapseSameLoc]);

  const layoutNodes = useMemo(
    () => (snap ? snap.nodes.filter((n) => visible.has(n.id)) : []),
    [snap, visible],
  );
  const layoutEdges = useMemo(
    () =>
      snap
        ? snap.edges.filter((e) => visible.has(e.from) && visible.has(e.to))
        : [],
    [snap, visible],
  );

  const positions = useForceLayout(layoutNodes, layoutEdges);
  const positionCount = Object.keys(positions).length;
  const structureKey = useMemo(() => {
    if (!snap) return "";
    return `${layoutNodes.map((n) => n.id).join(",")}|${layoutEdges
      .map((e) => `${e.from}->${e.to}:${e.dir}`)
      .join(",")}|${sel.collapseSameLoc}`;
  }, [layoutEdges, layoutNodes, sel.collapseSameLoc, snap]);

  useEffect(() => {
    if (positionCount === 0 || !structureKey) return;
    const frame = requestAnimationFrame(() => {
      void flow.fitView({ padding: 0.28, duration: 240 });
    });
    return () => cancelAnimationFrame(frame);
  }, [flow, positionCount, structureKey]);

  const apply = useCallback((next: SessionSnapshot) => {
    setSnap(next);
    setSel((s) => ({ ...s, focus: next.focus, edgeKey: null }));
  }, []);

  const head = snap?.work[0];
  const canStep = Boolean(
    snap && snap.status === "running" && !busy && sel.focus === head,
  );
  const canRun = Boolean(snap && snap.status === "running" && !busy);
  const done = useMemo(() => (snap ? processedIds(snap) : new Set<number>()), [snap]);

  const focusedSplit = useMemo(() => {
    if (!focusedNode || !snap) return null;
    return splitExprs(focusedNode, snap.nodes);
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
      apply(await stepSession(snap.id));
    } catch (err: unknown) {
      setError(err instanceof Error ? err.message : "step failed");
    } finally {
      setBusy(false);
    }
  }, [apply, sel.focus, snap]);

  const onRun = useCallback(async () => {
    if (!snap || snap.status !== "running") return;
    setBusy(true);
    setError(null);
    try {
      apply(await runSession(snap.id));
    } catch (err: unknown) {
      setError(err instanceof Error ? err.message : "run failed");
    } finally {
      setBusy(false);
    }
  }, [apply, snap]);

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
    const out: StateFlowNode[] = [];
    for (const node of layoutNodes) {
      const id = String(node.id);
      const pos = positions[id];
      if (!pos) continue;
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
          entry: node.id === 0,
          processed: done.has(node.id),
          hasHelper: node.predicates.some((p) => p.kind === "helper"),
          hasPacket: node.exprs.some((e) => parseReg(e.reg).kind === "packet"),
          hasRet: node.predicates.some((p) => p.kind === "ret"),
        },
        draggable: false,
      });
    }
    return out.length === 0 ? EMPTY_FLOW_NODES : out;
  }, [done, layoutNodes, positions, sel.compare, sel.focus, snap]);

  const flowEdges = useMemo<Edge[]>(() => {
    if (!snap || flowNodes.length === 0) return EMPTY_FLOW_EDGES;
    const placed = new Set(flowNodes.map((n) => n.id));
    const next = layoutEdges
      .filter((edge) => placed.has(String(edge.from)) && placed.has(String(edge.to)))
      .map((edge) => {
        const id = edgeKey(edge);
        const branch = edge.dir === "taken" || edge.dir === "not_taken";
        return {
          id,
          source: String(edge.from),
          target: String(edge.to),
          sourceHandle: "r",
          targetHandle: "l",
          type: "default",
          label: edge.dir === "only" ? undefined : edge.dir,
          className: `flow-edge${branch ? " flow-edge--branch" : ""}${
            sel.edgeKey === id ? " flow-edge--sel" : ""
          }`,
          labelStyle: { fill: "#c9bfb0", fontSize: 10 },
        };
      });
    return next.length === 0 ? EMPTY_FLOW_EDGES : next;
  }, [flowNodes, layoutEdges, sel.edgeKey, snap]);

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
    const src = snap.edges.find((e) => e.dir === "taken")?.from;
    if (src === undefined) return;
    setSel((s) => ({ ...s, focus: src, panel: "node", edgeKey: null }));
  }, [snap]);

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
          max={512}
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
        <label className="muted collapse-toggle">
          <input
            type="checkbox"
            checked={sel.collapseSameLoc}
            onChange={(ev) =>
              setSel((s) => ({ ...s, collapseSameLoc: ev.target.checked }))
            }
          />
          折叠同位置（仅视图）
        </label>
        <Text className="mono muted" fontSize={11}>
          快照不可变 · Shift+点击设比较节点 · {snap?.proof_note ?? ""}
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
        </Box>

        <Flex className="panel panel--right" width={400} flexDirection="column" minHeight={0}>
          <Flex className="panel-tabs" gap={6} px={10} pt={10}>
            {(
              [
                ["node", "节点"],
                ["step", "单步"],
                ["path", "路径"],
                ["compare", "比较"],
                ["dual", "双架构"],
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

          <Box className="panel__body" flex="1" overflow="auto" minHeight={0} px={14} pb={10}>
            {sel.panel === "node" && focusedNode && focusedSplit ? (
              <>
                <Text className="sem-heading">
                  执行前快照 · #{focusedNode.id} ·{" "}
                  {focusedNode.loc === "exit" ? "exit（终态）" : `pos ${focusedNode.loc}`}
                </Text>
                <Text className="sem-sub">Expr（按 RegKind）</Text>
                <ExprGroups exprs={focusedSplit.eg} />
                {focusedSplit.eiIn.length > 0 ? (
                  <>
                    <Text className="sem-sub sem-sub--gap">到达 Δ（eiIn）</Text>
                    <ExprGroups exprs={focusedSplit.eiIn} />
                  </>
                ) : null}
                {focusedSplit.eiOut.length > 0 ? (
                  <>
                    <Text className="sem-sub sem-sub--gap">展开写出（eiOut）</Text>
                    <ExprGroups exprs={focusedSplit.eiOut} />
                  </>
                ) : null}
                <Text className="sem-sub sem-sub--gap">Predicate</Text>
                <PredList preds={focusedNode.predicates} />
                {dualTakenNotTaken ? (
                  <>
                    <Text className="sem-sub sem-sub--gap">出边 Taken / NotTaken</Text>
                    <Text className="mono sem-line" display="block">
                      Taken →{" "}
                      {dualTakenNotTaken.taken.map((e) => `#${e.to}`).join(", ") || "∅"}
                    </Text>
                    <Text className="mono sem-line" display="block">
                      NotTaken →{" "}
                      {dualTakenNotTaken.notTaken.map((e) => `#${e.to}`).join(", ") ||
                        "∅"}
                    </Text>
                  </>
                ) : null}
              </>
            ) : null}

            {sel.panel === "step" && snap ? (
              <>
                <Text className="sem-heading">单步 / 边详情</Text>
                {selectedEdge ? (
                  <>
                    <Text className="mono sem-line" display="block">
                      {selectedEdge.from} —{selectedEdge.dir}→ {selectedEdge.to}
                    </Text>
                    {(() => {
                      const src = snap.nodes.find((n) => n.id === selectedEdge.from);
                      const dst = snap.nodes.find((n) => n.id === selectedEdge.to);
                      if (!src || !dst) return null;
                      const delta = localExprs(src.exprs, dst.exprs);
                      return (
                        <>
                          <Text className="sem-sub">源执行前 Expr 条数 {src.exprs.length}</Text>
                          <Text className="sem-sub">目标执行前（到达后）Δ</Text>
                          <ExprGroups exprs={delta} />
                          <Text className="sem-sub sem-sub--gap">目标 Predicate</Text>
                          <PredList preds={dst.predicates} />
                        </>
                      );
                    })()}
                  </>
                ) : (
                  <Text className="muted">点击图上的边查看局部效果与目标快照。</Text>
                )}
                <Text className="sem-sub sem-sub--gap">当前节点入边</Text>
                {focusedNode
                  ? inboundEdges(focusedNode.id, snap.edges).map((e) => (
                      <Text key={edgeKey(e)} className="mono sem-line" display="block">
                        #{e.from} —{e.dir}→ #{e.to}
                      </Text>
                    ))
                  : null}
              </>
            ) : null}

            {sel.panel === "path" && snap ? (
              <>
                <Text className="sem-heading">路径（root → focus）</Text>
                <Text className="mono muted" display="block">
                  {pathIds.map((id) => `#${id}`).join(" → ")}
                </Text>
                {pathIds.map((id) => {
                  const n = snap.nodes.find((x) => x.id === id);
                  if (!n) return null;
                  return (
                    <Box key={id} className="path-card">
                      <Text className="mono sem-line" display="block">
                        #{id} loc={n.loc} E={n.exprs.length} P={n.predicates.length}
                      </Text>
                      <PredList preds={n.predicates} />
                    </Box>
                  );
                })}
              </>
            ) : null}

            {sel.panel === "compare" ? (
              <>
                <Text className="sem-heading">两节点比较</Text>
                <Text className="muted" display="block">
                  焦点 #{sel.focus}
                  {sel.compare !== null ? ` · 比较 #${sel.compare}` : " · Shift+点击选第二节点"}
                </Text>
                {focusedNode && compareNode ? (
                  <>
                    <Text className="sem-sub">
                      同位置？{" "}
                      {focusedNode.loc === compareNode.loc
                        ? `是 (loc ${focusedNode.loc})，引用不同`
                        : "否"}
                    </Text>
                    {(() => {
                      const d = diffExprs(focusedNode.exprs, compareNode.exprs);
                      const pd = diffPredicates(
                        focusedNode.predicates,
                        compareNode.predicates,
                      );
                      return (
                        <>
                          <Text className="sem-sub">Expr 新增 {d.added.length}</Text>
                          {d.added.map((e, i) => (
                            <ExprDetail key={`a${i}`} e={e} />
                          ))}
                          <Text className="sem-sub">Expr 删除 {d.removed.length}</Text>
                          {d.removed.map((e, i) => (
                            <ExprDetail key={`r${i}`} e={e} />
                          ))}
                          <Text className="sem-sub">Expr 覆写 {d.changed.length}</Text>
                          {d.changed.map((c, i) => (
                            <Box key={`c${i}`}>
                              <Text className="mono muted" display="block">
                                before {c.before.term}
                              </Text>
                              <ExprDetail e={c.after} />
                            </Box>
                          ))}
                          <Text className="sem-sub sem-sub--gap">
                            Predicate +{pd.added.length} / −{pd.removed.length}
                          </Text>
                          {pd.added.map((p, i) => (
                            <Box key={`pa${i}`}>
                              <Text className="mono muted" display="block">
                                +
                              </Text>
                              <PredDetail p={p} />
                            </Box>
                          ))}
                          {pd.removed.map((p, i) => (
                            <Box key={`pr${i}`}>
                              <Text className="mono muted" display="block">
                                −
                              </Text>
                              <PredDetail p={p} />
                            </Box>
                          ))}
                        </>
                      );
                    })()}
                  </>
                ) : (
                  <Text className="muted">需要两个节点引用。</Text>
                )}
              </>
            ) : null}

            {sel.panel === "dual" ? (
              <>
                <Text className="sem-heading">双架构比较</Text>
                <Text className="fail-banner" display="block">
                  未实现
                </Text>
                <Text className="muted" display="block">
                  eBPF 侧 Step / 观察投影尚未接入核心。此处不伪造一致性结论。
                </Text>
              </>
            ) : null}

            {!focusedNode && sel.panel !== "dual" ? (
              <Text className="muted">等待节点…</Text>
            ) : null}
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

      <Flex className="toolbar" alignItems="center" justifyContent="center" gap={12}>
        <Button
          type="button"
          className="toolbar__btn"
          onClick={() => void onStep()}
          disabled={!canStep}
          opacity={canStep ? 1 : 0.45}
        >
          单步（Work 首）
        </Button>
        <Button
          type="button"
          className="toolbar__btn"
          onClick={() => void onRun()}
          disabled={!canRun}
          opacity={canRun ? 1 : 0.45}
        >
          运行到结束
        </Button>
        <Text className="mono toolbar__status">
          {snap
            ? `${statusLabel[snap.status]}  fuel ${snap.fuel}/${snap.budget}  ${
                snap.arch
              }  ${snap.program}${snap.reason ? `  ${snap.reason}` : ""}`
            : "连接中"}
        </Text>
      </Flex>
    </Flex>
  );
}
