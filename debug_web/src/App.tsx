import { Box, Button, Flex, Text } from "@kuma-ui/core";
import {
  Background,
  ReactFlow,
  ReactFlowProvider,
  useReactFlow,
  type Edge,
  type NodeMouseHandler,
} from "@xyflow/react";
import { useCallback, useEffect, useMemo, useRef, useState } from "react";
import "@xyflow/react/dist/style.css";
import { createSession, runSession, stepSession } from "./api";
import { StateNodeView, type StateFlowNode } from "./StateNode";
import type { SessionSnapshot } from "./types";
import { useForceLayout } from "./useForceLayout";

const nodeTypes = { state: StateNodeView };

const statusLabel: Record<SessionSnapshot["status"], string> = {
  running: "进行中",
  complete: "完成",
  fail: "失败",
};

export function App() {
  return (
    <ReactFlowProvider>
      <DebugScreen />
    </ReactFlowProvider>
  );
}

function DebugScreen() {
  const [snap, setSnap] = useState<SessionSnapshot | null>(null);
  const [focus, setFocus] = useState(0);
  const [busy, setBusy] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const insnRef = useRef<HTMLDivElement | null>(null);
  const logRef = useRef<HTMLDivElement | null>(null);
  const flow = useReactFlow();

  useEffect(() => {
    let alive = true;
    createSession(11)
      .then((next) => {
        if (!alive) return;
        setSnap(next);
        setFocus(next.focus);
      })
      .catch((err: unknown) => {
        if (!alive) return;
        setError(err instanceof Error ? err.message : "session failed");
      });
    return () => {
      alive = false;
    };
  }, []);

  useEffect(() => {
    insnRef.current?.scrollIntoView({ block: "nearest" });
  }, [snap?.cursor_j, snap?.insns.length]);

  useEffect(() => {
    logRef.current?.scrollIntoView({ block: "end" });
  }, [snap?.log.length]);

  const graphKey = snap
    ? `${snap.id}:${snap.nodes.length}:${snap.edges.length}:${snap.fuel}`
    : "";
  const positions = useForceLayout(snap?.nodes ?? [], snap?.edges ?? [], graphKey);

  useEffect(() => {
    if (!snap) return;
    const frame = requestAnimationFrame(() => {
      void flow.fitView({ padding: 0.28, duration: 220 });
    });
    return () => cancelAnimationFrame(frame);
  }, [flow, snap?.id, snap?.nodes.length]);

  const apply = useCallback((next: SessionSnapshot) => {
    setSnap(next);
    setFocus(next.focus);
  }, []);

  const head = snap?.work[0];
  const canStep = Boolean(snap && snap.status === "running" && !busy && focus === head);
  const canRun = Boolean(snap && snap.status === "running" && !busy);
  const focusedNode = snap?.nodes.find((node) => node.id === focus) ?? null;

  const onStep = useCallback(async () => {
    if (!snap || snap.status !== "running" || snap.work[0] !== focus) return;
    setBusy(true);
    setError(null);
    try {
      apply(await stepSession(snap.id));
    } catch (err: unknown) {
      setError(err instanceof Error ? err.message : "step failed");
    } finally {
      setBusy(false);
    }
  }, [apply, focus, snap]);

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

  const onNodeClick = useCallback<NodeMouseHandler>(
    (_event, node) => {
      const id = Number(node.id);
      if (focus === id && snap?.work[0] === id && snap.status === "running") {
        void onStep();
        return;
      }
      setFocus(id);
    },
    [focus, onStep, snap],
  );

  const flowNodes = useMemo<StateFlowNode[]>(() => {
    if (!snap) return [];
    const headId = snap.work[0];
    return snap.nodes.map((node) => {
      const id = String(node.id);
      const pos = positions[id] ?? { x: 0, y: 0 };
      return {
        id,
        type: "state",
        position: { x: pos.x, y: pos.y },
        data: {
          loc: node.loc,
          exprCount: node.exprs.length,
          predCount: node.predicates.length,
          focused: node.id === focus,
          head: node.id === headId,
        },
        draggable: false,
      };
    });
  }, [focus, positions, snap]);

  const flowEdges = useMemo<Edge[]>(() => {
    if (!snap) return [];
    return snap.edges.map((edge) => ({
      id: `${edge.from}-${edge.to}`,
      source: String(edge.from),
      target: String(edge.to),
      label: edge.dir,
      className: "flow-edge",
      labelStyle: { fill: "#c9bfb0", fontSize: 11 },
    }));
  }, [snap]);

  return (
    <Flex className="app-shell" height="100%" flexDirection="column">
      <Flex flex="1" minHeight={0} gap={12} p={12}>
        <Flex className="panel panel--left" width={300} flexDirection="column" minHeight={0}>
          <Text className="panel__title">指令列表</Text>
          <Box className="panel__body" flex="1" overflow="auto" minHeight={0}>
            {snap?.insns.map((insn) => {
              const current = insn.j === snap.cursor_j;
              return (
                <Box
                  key={insn.j}
                  ref={current ? insnRef : undefined}
                  className={`insn-row${current ? " insn-row--current" : ""}`}
                >
                  <Text className="mono insn-row__text">{insn.text}</Text>
                </Box>
              );
            })}
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
            nodesDraggable={false}
            nodesFocusable={false}
            elementsSelectable={false}
            fitView
            proOptions={{ hideAttribution: false }}
            colorMode="dark"
          >
            <Background color="rgba(120,112,98,0.35)" gap={24} />
          </ReactFlow>
        </Box>

        <Flex className="panel panel--right" width={360} flexDirection="column" minHeight={0}>
          <Text className="panel__title">状态</Text>
          <Box className="panel__body" flex="1" overflow="auto" minHeight={0} px={14} pb={10}>
            {focusedNode ? (
              <>
                <Text className="sem-heading">
                  σ = (E, P) · node {focusedNode.id} ·{" "}
                  {focusedNode.loc === "exit" ? "exit" : `pos ${focusedNode.loc}`}
                </Text>
                <Text className="sem-sub">Exprs E</Text>
                {focusedNode.exprs.length === 0 ? (
                  <Text className="mono muted">∅</Text>
                ) : (
                  focusedNode.exprs.map((expr, index) => (
                    <Text key={`${expr.reg}-${index}`} className="mono sem-line" display="block">
                      {expr.reg} {expr.rel} {expr.term}
                    </Text>
                  ))
                )}
                <Text className="sem-sub sem-sub--gap">
                  Predicates P
                </Text>
                {focusedNode.predicates.length === 0 ? (
                  <Text className="mono muted">∅</Text>
                ) : (
                  focusedNode.predicates.map((pred) => (
                    <Text key={pred.tag} className="mono sem-line" display="block">
                      tag {pred.tag}
                    </Text>
                  ))
                )}
              </>
            ) : (
              <Text className="muted">等待节点…</Text>
            )}
          </Box>
          <Box className="log-strip">
            <Text className="panel__title panel__title--small">日志</Text>
            <Box className="log-strip__body" maxHeight={140} overflow="auto" px={12} pb={10}>
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
          单步调试
        </Button>
        <Button
          type="button"
          className="toolbar__btn"
          onClick={() => void onRun()}
          disabled={!canRun}
          opacity={canRun ? 1 : 0.45}
        >
          到底调试
        </Button>
        <Text className="mono toolbar__status">
          {snap
            ? `${statusLabel[snap.status]}  fuel ${snap.fuel}/${snap.budget}${
                snap.reason ? `  ${snap.reason}` : ""
              }`
            : "连接中"}
        </Text>
      </Flex>
    </Flex>
  );
}
