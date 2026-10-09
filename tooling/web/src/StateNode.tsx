import { Handle, Position, type Node, type NodeProps } from "@xyflow/react";

export type StateNodeData = {
  nodeId: number;
  loc: string;
  egCount: number;
  predCount: number;
  focused: boolean;
  compare: boolean;
  head: boolean;
  entry: boolean;
  processed: boolean;
  failed: boolean;
  hasHelper: boolean;
  hasPacket: boolean;
  hasRet: boolean;
};

export type StateFlowNode = Node<StateNodeData, "state">;

const handleStyle = { opacity: 0, width: 8, height: 8 };

export function StateNodeView({ data }: NodeProps<StateFlowNode>) {
  return (
    <div
      className={`state-node${data.focused ? " state-node--focus" : ""}${
        data.compare ? " state-node--compare" : ""
      }${data.head ? " state-node--head" : ""}${data.entry ? " state-node--entry" : ""}${
        data.processed ? " state-node--done" : ""
      }${data.failed ? " state-node--failed" : ""}`}
    >
      <Handle id="l" type="target" position={Position.Left} style={handleStyle} />
      <Handle id="r" type="source" position={Position.Right} style={handleStyle} />
      <div className="state-node__loc">
        #{data.nodeId} · {data.loc === "exit" ? "exit" : `pos ${data.loc}`}
      </div>
      <div className="state-node__meta">
        E={data.egCount} · P={data.predCount}
        {data.hasHelper ? " · H" : ""}
        {data.hasPacket ? " · Pk" : ""}
        {data.hasRet ? " · R" : ""}
      </div>
      {data.entry ? <div className="state-node__badge">入口</div> : null}
      {data.head ? <div className="state-node__head">Work 首</div> : null}
      {data.failed ? (
        <div className="state-node__badge">拒绝</div>
      ) : data.processed && !data.head ? (
        <div className="state-node__badge">已处理</div>
      ) : null}
    </div>
  );
}
