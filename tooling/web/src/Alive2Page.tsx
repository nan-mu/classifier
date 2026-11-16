import { useState } from "react";
import { alive2Layout, selectedNode, type AliveGraph } from "./alive2Graph";

const SAMPLE = `; alive-file v1
define i64 @branch() memory(none) {
entry:
  %c = icmp eq i64 1, 1
  br i1 %c, label %yes, label %no
yes:
  ret i64 7
no:
  ret i64 0
}
`;

async function readError(res: Response): Promise<string> {
  const text = await res.text();
  try {
    const body = JSON.parse(text) as { code?: string; message?: string };
    return `${body.code ?? res.status}: ${body.message ?? text}`;
  } catch {
    return `${res.status}: ${text}`;
  }
}

export function Alive2Page() {
  const [ir, setIr] = useState(SAMPLE);
  const [graph, setGraph] = useState<AliveGraph | null>(null);
  const [picked, setPicked] = useState<string | null>(null);
  const [error, setError] = useState("");
  const layout = alive2Layout;
  const node = graph ? selectedNode(graph, picked) : null;

  async function createRun() {
    setError("");
    const created = await fetch("/api/alive2/runs", {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({ ir_text: ir, unroll_bound: 1 }),
    });
    if (!created.ok) {
      setError(await readError(created));
      return;
    }
    const body = (await created.json()) as { id: string };
    const loaded = await fetch(`/api/alive2/runs/${body.id}/graph`);
    if (!loaded.ok) {
      setError(await readError(loaded));
      return;
    }
    const next = (await loaded.json()) as AliveGraph;
    setGraph(next);
    setPicked(next.nodes[0]?.id ?? null);
  }

  return (
    <div className="alive2">
      <style>{`
        .alive2 { height: 100vh; display: grid; grid-template-rows: ${layout.header}px ${layout.toolbar}px 1fr; }
        .alive2 header, .alive2 .bar { display: flex; align-items: center; padding: 0 16px; border-bottom: 1px solid #ddd; }
        .alive2 .columns { display: grid; grid-template-columns: minmax(${layout.leftMin}px, ${layout.left}px) 1fr minmax(${layout.rightMin}px, ${layout.right}px); min-height: 0; }
        .alive2 aside, .alive2 main { overflow: auto; border-right: 1px solid #ddd; padding: 12px; }
        .alive2 button { margin-right: 8px; }
        .alive2 .node { display: block; width: 100%; text-align: left; margin-bottom: 4px; }
        @media (max-width: ${layout.collapse - 1}px) {
          .alive2 .columns { grid-template-columns: 1fr; }
        }
      `}</style>
      <header>Alive2 状态图</header>
      <div className="bar">
        <button type="button" onClick={() => void createRun()}>创建运行</button>
        <span>{graph ? `run ${graph.run.status} / truncation ${graph.run.truncation.kind}` : "还没有运行"}</span>
      </div>
      <div className="columns">
        <aside>
          <p>程序</p>
          <textarea value={ir} onChange={(event) => setIr(event.target.value)} rows={16} style={{ width: "100%" }} />
          {error ? <p>{error}</p> : null}
        </aside>
        <main>
          {graph?.nodes.map((item) => (
            <button key={item.id} type="button" className="node" onClick={() => setPicked(item.id)}>
              {item.id} {item.location.block} {item.state}
            </button>
          ))}
        </main>
        <aside>
          <p>节点</p>
          {node ? (
            <pre>{JSON.stringify(node, null, 2)}</pre>
          ) : (
            <p>未选择</p>
          )}
          <p>edges</p>
          <ul>
            {graph?.edges.map((edge) => (
              <li key={edge.id}>{edge.kind} {edge.from} → {edge.to} guard {edge.guard}</li>
            ))}
          </ul>
          <p>coverage {graph?.coverage.all_inputs_covered ?? "not_established"}</p>
        </aside>
      </div>
    </div>
  );
}
