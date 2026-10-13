import { Handle, Position, type Node, type NodeProps } from "@xyflow/react";
import type { NodeRole } from "./nodeRole";

export type StateNodeData = {
  nodeId: number;
  loc: string;
  egCount: number;
  predCount: number;
  focused: boolean;
  compare: boolean;
  head: boolean;
  processed: boolean;
  role: NodeRole;
  /** 节点类型 chips (first line). */
  tags: string[];
  insnHint?: string;
  foldedCount?: number;
  /** Load/store family: bottom wash + reg-kind accent. */
  accessFamily: boolean;
};

export type StateFlowNode = Node<StateNodeData, "state">;

const handleStyle = { opacity: 0, width: 8, height: 8 };

export function StateNodeView({ data }: NodeProps<StateFlowNode>) {
  const loc = data.loc === "exit" ? "exit" : `pos ${data.loc}`;
  const tagLine = data.tags.join(" · ");
  const title = [
    tagLine,
    `#${data.nodeId}`,
    loc,
    data.insnHint,
    `E=${data.egCount} P=${data.predCount}`,
    data.foldedCount && data.foldedCount > 1 ? `折叠×${data.foldedCount}` : null,
    data.head ? "Work 首" : null,
  ]
    .filter(Boolean)
    .join(" · ");

  return (
    <div
      className={`state-node state-node--role-${data.role}${
        data.accessFamily ? " state-node--access" : ""
      }${data.focused ? " state-node--focus" : ""}${
        data.compare ? " state-node--compare" : ""
      }${data.head ? " state-node--head" : ""}${
        data.processed ? " state-node--done" : ""
      }${data.foldedCount && data.foldedCount > 1 ? " state-node--folded" : ""}`}
      title={title}
    >
      <Handle id="l" type="target" position={Position.Left} style={handleStyle} />
      <Handle id="r" type="source" position={Position.Right} style={handleStyle} />
      <div className="state-node__header">
        <span className="state-node__tags">{tagLine}</span>
        {data.head ? <span className="state-node__head">Work</span> : null}
      </div>
      <div className="state-node__title">
        #{data.nodeId}
        <span className="state-node__loc"> · {loc}</span>
        {data.foldedCount && data.foldedCount > 1 ? (
          <span className="state-node__fold"> · ×{data.foldedCount}</span>
        ) : null}
      </div>
      <div className="state-node__meta">
        {data.insnHint ? (
          <span className="state-node__insn">{data.insnHint}</span>
        ) : null}
        {data.insnHint ? <span className="state-node__dot"> · </span> : null}
        <span>
          E={data.egCount} · P={data.predCount}
        </span>
      </div>
    </div>
  );
}
