import { Handle, Position, type Node, type NodeProps } from "@xyflow/react";

export type StateNodeData = {
  loc: string;
  exprCount: number;
  predCount: number;
  focused: boolean;
  head: boolean;
};

export type StateFlowNode = Node<StateNodeData, "state">;

export function StateNodeView({ data }: NodeProps<StateFlowNode>) {
  return (
    <div
      className={`state-node${data.focused ? " state-node--focus" : ""}${
        data.head ? " state-node--head" : ""
      }`}
    >
      <Handle type="target" position={Position.Top} style={{ opacity: 0 }} />
      <div className="state-node__loc">
        {data.loc === "exit" ? "exit" : `pos ${data.loc}`}
      </div>
      <div className="state-node__meta">
        E={data.exprCount} · P={data.predCount}
      </div>
      {data.head ? <div className="state-node__head">队列首</div> : null}
      <Handle type="source" position={Position.Bottom} style={{ opacity: 0 }} />
    </div>
  );
}
