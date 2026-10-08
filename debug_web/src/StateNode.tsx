import { Handle, Position, type Node, type NodeProps } from "@xyflow/react";

export type StateNodeData = {
  loc: string;
  r: number;
  focused: boolean;
  head: boolean;
};

export type StateFlowNode = Node<StateNodeData, "state">;

export function StateNodeView({ data }: NodeProps<StateFlowNode>) {
  return (
    <div
      style={{
        minWidth: 148,
        padding: "8px 10px",
        background: "#2a2824",
        color: "#e8e2d6",
        border: data.focused ? "3px solid #f3efe4" : "1px solid #4a463f",
        borderRadius: 2,
        fontFamily: "ui-monospace, SFMono-Regular, Menlo, monospace",
        fontSize: 12,
        lineHeight: 1.45,
      }}
    >
      <Handle type="target" position={Position.Top} style={{ opacity: 0 }} />
      <div>{data.loc === "exit" ? "exit" : `pos ${data.loc}`}</div>
      <div>r = {data.r}</div>
      {data.head ? <div style={{ color: "#c4b49a" }}>队列首</div> : null}
      <Handle type="source" position={Position.Bottom} style={{ opacity: 0 }} />
    </div>
  );
}
