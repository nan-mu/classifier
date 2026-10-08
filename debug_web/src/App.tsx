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

  useEffect(() => {
    if (!snap) return;
    const frame = requestAnimationFrame(() => {
      void flow.fitView({ padding: 0.25, duration: 180 });
    });
    return () => cancelAnimationFrame(frame);
  }, [flow, snap]);

  const apply = useCallback((next: SessionSnapshot) => {
    setSnap(next);
    setFocus(next.focus);
  }, []);

  const head = snap?.work[0];
  const canStep = Boolean(snap && snap.status === "running" && !busy && focus === head);
  const canRun = Boolean(snap && snap.status === "running" && !busy);

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
    return snap.nodes.map((node) => ({
      id: String(node.id),
      type: "state",
      position: { x: node.x, y: node.y },
      data: {
        loc: node.loc,
        r: node.r,
        focused: node.id === focus,
        head: node.id === headId,
      },
      draggable: false,
    }));
  }, [focus, snap]);

  const flowEdges = useMemo<Edge[]>(() => {
    if (!snap) return [];
    return snap.edges.map((edge) => ({
      id: `${edge.from}-${edge.to}`,
      source: String(edge.from),
      target: String(edge.to),
      label: edge.dir,
      style: { stroke: "#8d8476" },
      labelStyle: { fill: "#b7ad9e", fontSize: 11 },
    }));
  }, [snap]);

  return (
    <Flex height="100%" flexDirection="column" bg="#1c1b19" color="#e7e2d6">
      <Flex flex="1" minHeight={0}>
        <Flex
          width={280}
          flexDirection="column"
          borderRight="1px solid #3c3834"
          bg="#221f1c"
          minHeight={0}
        >
          <Text px={12} py={10} fontSize={13} color="#d9d0c2">
            指令列表
          </Text>
          <Box flex="1" overflow="auto" minHeight={0}>
            {snap?.insns.map((insn) => {
              const current = insn.j === snap.cursor_j;
              return (
                <Box
                  key={insn.j}
                  ref={current ? insnRef : undefined}
                  px={12}
                  py={8}
                  bg={current ? "#3a3428" : "transparent"}
                  borderLeft={current ? "3px solid #d8c7a2" : "3px solid transparent"}
                >
                  <Text
                    fontFamily="ui-monospace, SFMono-Regular, Menlo, monospace"
                    fontSize={12}
                    color="#e8e2d6"
                  >
                    {insn.j}: {insn.text}
                  </Text>
                </Box>
              );
            })}
          </Box>
        </Flex>

        <Box flex="1" minWidth={0} position="relative">
          {error ? (
            <Text p={16} fontSize={13} color="#e0b4a4">
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
            <Background color="#3a3832" gap={22} />
          </ReactFlow>
        </Box>

        <Flex
          width={340}
          flexDirection="column"
          borderLeft="1px solid #3c3834"
          bg="#221f1c"
          minHeight={0}
        >
          <Text px={12} py={10} fontSize={13} color="#d9d0c2">
            状态
          </Text>
          <Box flex="1" overflow="auto" minHeight={0} px={12} pb={12}>
            {snap?.log.map((entry) => (
              <Text
                key={entry.t}
                display="block"
                py={4}
                fontFamily="ui-monospace, SFMono-Regular, Menlo, monospace"
                fontSize={12}
                color="#d5cec2"
                borderBottom="1px solid #34302c"
              >
                {entry.t}. {entry.msg}
              </Text>
            ))}
            <Box ref={logRef} />
          </Box>
        </Flex>
      </Flex>

      <Flex
        height={64}
        alignItems="center"
        justifyContent="center"
        gap={12}
        borderTop="1px solid #3c3834"
        bg="#221f1c"
      >
        <Button
          type="button"
          onClick={() => void onStep()}
          disabled={!canStep}
          px={16}
          py={8}
          bg="#2c2a26"
          color="#f0eadf"
          border="1px solid #6b6458"
          borderRadius={2}
          fontSize={14}
          opacity={canStep ? 1 : 0.45}
        >
          单步调试
        </Button>
        <Button
          type="button"
          onClick={() => void onRun()}
          disabled={!canRun}
          px={16}
          py={8}
          bg="#2c2a26"
          color="#f0eadf"
          border="1px solid #6b6458"
          borderRadius={2}
          fontSize={14}
          opacity={canRun ? 1 : 0.45}
        >
          到底调试
        </Button>
        <Text fontSize={12} color="#b7ad9e" fontFamily="ui-monospace, SFMono-Regular, Menlo, monospace">
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
