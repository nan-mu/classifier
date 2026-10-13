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
import {
  comparePredicates,
  createSession,
  runSessionStream,
  stepSession,
  type RunStreamStats,
} from "./api";
import { insnIndexForNode, splitExprs } from "./exprs";
import { formatExprMath, formatPredChip } from "./formatExpr";
import { foldSameTypeChains, resolveFoldedId } from "./collapse";
import {
  classifyNodeRole,
  insnMnemonic,
  insnTextForNode,
  NODE_ROLE_LEGEND,
} from "./nodeRole";
import { PredicateCompareView } from "./PredicateCompare";
import { StateNodeView, type StateFlowNode } from "./StateNode";
import type {
  ArchKind,
  PredMatchReport,
  PredRow,
  ExprRow,
  SessionSnapshot,
} from "./types";
import { toPredRun } from "./types";
import { useForceLayout } from "./useForceLayout";
import {
  branchSource,
  countBranchEdges,
  diffPredicates,
  edgeKey,
  formatPred,
  outboundEdges,
  parseEdgeKey,
  processedIds,
  visibleNodeIds,
  type ViewerSelection,
} from "./viewer";

type TabId = ArchKind | "compare";

type Snaps = {
  rv32imc: SessionSnapshot | null;
  ebpf: SessionSnapshot | null;
};

type RunSlot = {
  arch: ArchKind;
  label: string;
  snap: SessionSnapshot | null;
  stats: RunStreamStats | null;
};

type CompareUi =
  | { tag: "idle" }
  | { tag: "expanding"; left: RunSlot; right: RunSlot }
  | { tag: "ready"; report: PredMatchReport };

function emptySlot(arch: ArchKind): RunSlot {
  return {
    arch,
    label: arch === "rv32imc" ? "just_tx.elf" : "just_tx.bpf.o",
    snap: null,
    stats: null,
  };
}

function defaultName(arch: ArchKind): string {
  return arch === "ebpf" ? "just_tx.bpf.o" : "just_tx.elf";
}

function snapFresh(snap: SessionSnapshot | null, budget: number): snap is SessionSnapshot {
  return (
    snap != null
    && snap.budget === budget
    && (snap.status === "complete" || snap.status === "fail")
  );
}

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
          title={formatPred(p)}
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

function PiTag() {
  return (
    <>
      P<sub>i</sub>
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
  const [tab, setTab] = useState<TabId>("rv32imc");
  const [snaps, setSnaps] = useState<Snaps>({ rv32imc: null, ebpf: null });
  const [sel, setSel] = useState<ViewerSelection>({
    focus: 0,
    compare: null,
    edgeKey: null,
    collapseSameLoc: false,
    panel: "eg",
  });
  const [budget, setBudget] = useState(1024);
  const [firmwareName, setFirmwareName] = useState("just_tx.elf");
  const [firmwareBytes, setFirmwareBytes] = useState<ArrayBuffer | null>(null);
  const [busy, setBusy] = useState(false);
  const [streaming, setStreaming] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [runRate, setRunRate] = useState<string | null>(null);
  const [compareUi, setCompareUi] = useState<CompareUi>({ tag: "idle" });
  const insnRef = useRef<HTMLDivElement | null>(null);
  const logRef = useRef<HTMLDivElement | null>(null);
  const fileRef = useRef<HTMLInputElement | null>(null);
  const runAbortRef = useRef<AbortController | null>(null);
  const compareAbortRef = useRef<AbortController | null>(null);
  const pendingSnapRef = useRef<SessionSnapshot | null>(null);
  const rafRef = useRef<number | null>(null);
  const fitOnceRef = useRef(true);
  const tabRef = useRef<TabId>(tab);
  const snapsRef = useRef(snaps);
  const flow = useReactFlow();

  tabRef.current = tab;
  snapsRef.current = snaps;

  const archTab: ArchKind | null = tab === "compare" ? null : tab;
  const snap = archTab ? snaps[archTab] : null;
  const comparing = tab === "compare";

  const flushPendingSnap = useCallback(() => {
    rafRef.current = null;
    const next = pendingSnapRef.current;
    if (!next) return;
    pendingSnapRef.current = null;
    setSnaps((prev) => ({ ...prev, [next.arch]: next }));
    if (tabRef.current === next.arch) {
      setSel((s) => ({ ...s, focus: next.focus, edgeKey: null }));
    }
  }, []);

  const apply = useCallback(
    (next: SessionSnapshot, opts?: { immediate?: boolean }) => {
      if (opts?.immediate) {
        pendingSnapRef.current = null;
        if (rafRef.current != null) {
          cancelAnimationFrame(rafRef.current);
          rafRef.current = null;
        }
        setSnaps((prev) => ({ ...prev, [next.arch]: next }));
        if (tabRef.current === next.arch) {
          setSel((s) => ({ ...s, focus: next.focus, edgeKey: null }));
        }
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
        if (tabRef.current === nextArch) {
          setSel((s) => ({
            ...s,
            focus: next.focus,
            compare: null,
            edgeKey: null,
          }));
        }
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
      setFirmwareName(archTab ? defaultName(archTab) : "just_tx.elf");
      setFirmwareBytes(null);
      return;
    }
    void file.arrayBuffer().then((buf) => {
      setFirmwareName(file.name);
      setFirmwareBytes(buf);
    });
  }, [archTab]);

  const focusedNode = snap?.nodes.find((n) => n.id === sel.focus) ?? null;
  const highlightJ = useMemo(
    () => (snap ? insnIndexForNode(focusedNode, snap.nodes) : null),
    [focusedNode, snap],
  );

  useEffect(() => {
    if (streaming || comparing) return;
    insnRef.current?.scrollIntoView({ block: "center", behavior: "smooth" });
  }, [highlightJ, snap?.insns.length, streaming, comparing]);

  useEffect(() => {
    if (streaming || comparing) return;
    logRef.current?.scrollIntoView({ block: "end" });
  }, [snap?.log.length, streaming, comparing]);

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
    if (streaming || comparing || !hasPositions) return;
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
  }, [flow, streaming, comparing, layoutMode, snap?.id, hasPositions]);

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

  const focusedPi = useMemo(() => {
    if (!focusedNode || !snap) return [];
    const parent = snap.nodes.find((n) => focusedNode.preds.includes(n.id));
    if (!parent) return focusedNode.predicates;
    return diffPredicates(parent.predicates, focusedNode.predicates).added;
  }, [focusedNode, snap]);

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

  const runPredicateCompare = useCallback(async () => {
    runAbortRef.current?.abort();
    compareAbortRef.current?.abort();
    const ac = new AbortController();
    compareAbortRef.current = ac;
    setBusy(true);
    setStreaming(false);
    setError(null);
    setRunRate(null);

    try {
      let left = snapsRef.current.rv32imc;
      let right = snapsRef.current.ebpf;
      const needExpand = !snapFresh(left, budget) || !snapFresh(right, budget);

      if (needExpand) {
        setCompareUi({
          tag: "expanding",
          left: emptySlot("rv32imc"),
          right: emptySlot("ebpf"),
        });
        const patchSlot = (
          side: "left" | "right",
          snapNext: SessionSnapshot,
          stats: RunStreamStats,
        ) => {
          apply(snapNext);
          setCompareUi((prev) => {
            if (prev.tag !== "expanding") return prev;
            return {
              ...prev,
              [side]: { ...prev[side], snap: snapNext, stats },
            };
          });
        };
        const [left0, right0] = await Promise.all([
          createSession({ budget, arch: "rv32imc", name: "just_tx.elf" }),
          createSession({ budget, arch: "ebpf", name: "just_tx.bpf.o" }),
        ]);
        const [leftFinal, rightFinal] = await Promise.all([
          runSessionStream(left0.id, (s, stats) => patchSlot("left", s, stats), ac.signal),
          runSessionStream(right0.id, (s, stats) => patchSlot("right", s, stats), ac.signal),
        ]);
        left = leftFinal;
        right = rightFinal;
        apply(leftFinal, { immediate: true });
        apply(rightFinal, { immediate: true });
      }

      if (ac.signal.aborted || !left || !right) return;
      const report = await comparePredicates(toPredRun(left), toPredRun(right));
      if (ac.signal.aborted) return;
      setCompareUi({ tag: "ready", report });
    } catch (err: unknown) {
      if (!ac.signal.aborted) {
        setError(err instanceof Error ? err.message : "predicate compare failed");
        setCompareUi({ tag: "idle" });
      }
    } finally {
      if (compareAbortRef.current === ac) compareAbortRef.current = null;
      setBusy(false);
    }
  }, [apply, budget]);

  const onSelectTab = useCallback(
    (next: TabId) => {
      if (next === "compare") {
        setTab("compare");
        void runPredicateCompare();
        return;
      }
      compareAbortRef.current?.abort();
      compareAbortRef.current = null;
      setCompareUi({ tag: "idle" });
      setTab(next);
      fitOnceRef.current = true;
      const existing = snapsRef.current[next];
      if (existing) {
        setSel((s) => ({
          ...s,
          focus: existing.focus,
          compare: null,
          edgeKey: null,
        }));
      }
      if (!firmwareBytes) {
        setFirmwareName(defaultName(next));
      }
    },
    [firmwareBytes, runPredicateCompare],
  );

  const onNodeClick = useCallback<NodeMouseHandler>((event, node) => {
    const id = Number(node.id);
    if (event.shiftKey) {
      setSel((s) => ({
        ...s,
        compare: s.compare === id ? null : id,
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
      panel: "ei",
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
    setSel((s) => ({ ...s, focus: src, panel: "eg", edgeKey: null }));
  }, [sel.focus, snap]);

  return (
    <Flex className="app-shell" height="100%" flexDirection="column">
      <Flex className="topbar" alignItems="center" gap={10} px={12} pt={10}>
        <div className="arch-tabs" role="tablist" aria-label="视图">
          {(
            [
              ["rv32imc", "RV32IMC"],
              ["ebpf", "eBPF"],
              ["compare", "对比"],
            ] as const
          ).map(([id, label]) => (
            <button
              key={id}
              type="button"
              role="tab"
              aria-selected={tab === id}
              className={`arch-tab${tab === id ? " arch-tab--on" : ""}`}
              onClick={() => onSelectTab(id)}
            >
              {label}
            </button>
          ))}
        </div>

        {!comparing ? (
          <>
            <Text className="muted">XDP ELF</Text>
            <label className="toolbar__file">
              <input
                ref={fileRef}
                type="file"
                accept=".elf,.o"
                disabled={busy}
                onChange={onFirmwarePick}
              />
              <span className="toolbar__file-btn">选择文件</span>
            </label>
            <Text className="mono muted" fontSize={11} title={firmwareName}>
              {firmwareBytes
                ? firmwareName
                : `${archTab ? defaultName(archTab) : "just_tx.elf"}（默认）`}
            </Text>
            {firmwareBytes ? (
              <Button
                type="button"
                className="toolbar__btn toolbar__btn--quiet"
                disabled={busy}
                onClick={() => {
                  setFirmwareName(archTab ? defaultName(archTab) : "just_tx.elf");
                  setFirmwareBytes(null);
                  if (fileRef.current) fileRef.current.value = "";
                }}
              >
                恢复默认
              </Button>
            ) : null}
          </>
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

        {!comparing && archTab ? (
          <Button
            type="button"
            className="toolbar__btn"
            disabled={busy}
            onClick={() =>
              void boot(archTab, budget, firmwareName, firmwareBytes)
            }
          >
            新建运行
          </Button>
        ) : null}

        {compareUi.tag === "expanding" ? (
          <Button
            type="button"
            className="toolbar__btn toolbar__btn--quiet"
            onClick={() => {
              compareAbortRef.current?.abort();
              setCompareUi({ tag: "idle" });
              setBusy(false);
            }}
          >
            停止
          </Button>
        ) : null}

        {compareUi.tag === "expanding" ? (
          <Flex flexDirection="column" gap={2} className="compare-progress">
            {(["left", "right"] as const).map((side) => {
              const slot = compareUi[side];
              return (
                <Text key={side} className="mono muted" fontSize={11}>
                  {slot.arch} · {slot.label} · steps {slot.stats?.steps ?? 0} · nodes{" "}
                  {slot.snap?.nodes.length ?? 0} · {slot.snap?.status ?? "…"}
                </Text>
              );
            })}
          </Flex>
        ) : (
          <Text className="mono muted" fontSize={11}>
            {comparing
              ? "Predicate heuristic · Term equality not proven"
              : `Shift+点击设比较 · 同类型自动折叠 · ${snap?.proof_note ?? ""}`}
          </Text>
        )}
      </Flex>

      {comparing ? (
        <Flex flex="1" minHeight={0} gap={12} p={12} pt={8}>
          {error ? (
            <Text className="error-banner" p={16} fontSize={13}>
              {error}
            </Text>
          ) : null}
          {compareUi.tag === "expanding" || compareUi.tag === "idle" ? (
            <Flex
              className="pred-compare panel"
              flex="1"
              alignItems="center"
              justifyContent="center"
            >
              <Text className="mono muted">
                {compareUi.tag === "expanding"
                  ? "并行展开 rv32imc / ebpf…"
                  : "准备 Predicate 比较…"}
              </Text>
            </Flex>
          ) : null}
          {compareUi.tag === "ready" ? (
            <PredicateCompareView report={compareUi.report} />
          ) : null}
        </Flex>
      ) : (
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
                  ["ei", <>E<sub>i</sub></>],
                  ["eg", <>E<sub>g</sub></>],
                  ["pi", <>P<sub>i</sub></>],
                  ["pg", <>P<sub>g</sub></>],
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

            <Box
              className="panel__body panel__body--state"
              flex="1"
              overflow="auto"
              minHeight={0}
              px={12}
              pb={8}
            >
              {focusedNode ? (
                <Text className="sem-heading">
                  #{focusedNode.id}
                  {focusedNode.loc === "exit" ? " · exit" : ` · pos ${focusedNode.loc}`}
                </Text>
              ) : null}

              {sel.panel === "ei" && focusedNode && focusedSplit ? (
                <>
                  {selectedEdge ? (
                    <Text className="mono muted" display="block" fontSize={11}>
                      {selectedEdge.from} —{selectedEdge.dir}→ {selectedEdge.to}
                    </Text>
                  ) : null}
                  {focusedSplit.eiIn.length > 0 ? (
                    <SemBlock tag={<EiTag />}>
                      <ExprCapsules exprs={focusedSplit.eiIn} />
                    </SemBlock>
                  ) : null}
                  {focusedSplit.eiOut
                    .filter((d) =>
                      selectedEdge
                        ? d.to === selectedEdge.to
                        : d.exprs.length > 0 || d.dir === "taken" || d.dir === "not_taken",
                    )
                    .map((delta) => (
                      <SemBlock key={delta.to} tag={<EiTag on={eiOnLabel(delta.dir)} />}>
                        <ExprCapsules exprs={delta.exprs} />
                      </SemBlock>
                    ))}
                  {focusedSplit.eiIn.length === 0
                  && focusedSplit.eiOut.every((d) => d.exprs.length === 0)
                  && !selectedEdge ? (
                    <SemBlock tag={<EiTag />}>
                      <ExprCapsules exprs={[]} />
                    </SemBlock>
                  ) : null}
                  {dualTakenNotTaken ? (
                    <Text className="mono muted" display="block" fontSize={11}>
                      T→{dualTakenNotTaken.taken.map((e) => e.to).join(",") || "∅"}
                      {" · "}
                      N→{dualTakenNotTaken.notTaken.map((e) => e.to).join(",") || "∅"}
                    </Text>
                  ) : null}
                </>
              ) : null}

              {sel.panel === "eg" && focusedNode && focusedSplit ? (
                <SemBlock tag={<EgTag />}>
                  <ExprCapsules exprs={focusedSplit.eg} />
                </SemBlock>
              ) : null}

              {sel.panel === "pi" && focusedNode ? (
                <SemBlock tag={<PiTag />}>
                  <PredCapsules preds={focusedPi} />
                </SemBlock>
              ) : null}

              {sel.panel === "pg" && focusedNode ? (
                <SemBlock tag={<PgTag />}>
                  <PredCapsules preds={focusedNode.predicates} />
                </SemBlock>
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
      )}
    </Flex>
  );
}
