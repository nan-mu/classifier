import { Handle, Position, type Node, type NodeProps } from "@xyflow/react";

export type StateNodeData = {
  loc: string;
  exprCount: number;
  predCount: number;
  focused: boolean;
  head: boolean;
};

export type StateFlowNode = Node<StateNodeData, "state">;

const handleStyle = { opacity: 0, width: 8, height: 8 };

/** Four-way handles so force-layout edges are not forced top→bottom. */
export function StateNodeView({ data }: NodeProps<StateFlowNode>) {
  return (
    <div
      className={`state-node${data.focused ? " state-node--focus" : ""}${
        data.head ? " state-node--head" : ""
      }`}
    >
      <Handle id="t" type="target" position={Position.Top} style={handleStyle} />
      <Handle id="l" type="target" position={Position.Left} style={handleStyle} />
      <Handle id="r" type="source" position={Position.Right} style={handleStyle} />
      <Handle id="b" type="source" position={Position.Bottom} style={handleStyle} />
      <div className="state-node__loc">
        {data.loc === "exit" ? "exit" : `pos ${data.loc}`}
      </div>
      <div className="state-node__meta">
        E={data.exprCount} · P={data.predCount}
      </div>
      {data.head ? <div className="state-node__head">队列首</div> : null}
    </div>
  );
}
