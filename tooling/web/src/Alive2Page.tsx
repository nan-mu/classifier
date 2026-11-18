import { useMemo, useState } from "react";
import { selectedNode, type AliveGraph, type AliveTerm } from "./alive2Graph";

const SAMPLE = `; alive-file v1
; alive2-pin adacbd5180ccf95075e9867c4f0c259f59c9fef2
; rocq-pin 78d65a77592aae84b31f86385f8be4ab83b45ccb
define i64 @branch(i64 %x) memory(none) {
entry:
  %c = icmp eq i64 %x, 0
  br i1 %c, label %yes, label %no
yes:
  ret i64 7
no:
  ret i64 9
}
`;

function readGraph(text: string): AliveGraph {
  const graph = JSON.parse(text) as AliveGraph;
  if (graph.schema !== "alive2-state-graph" || ![1, 2].includes(graph.schema_version ?? 0)
    || !Array.isArray(graph.nodes) || !Array.isArray(graph.edges) || !graph.run?.truncation || !graph.coverage) {
    throw new Error("Expected an alive2-state-graph JSON document (v1 or v2).");
  }
  const ids = new Set(graph.nodes.map((node) => node.id));
  if (ids.size !== graph.nodes.length || graph.nodes.some((node) => typeof node.id !== "string" || !node.location || !Number.isInteger(node.unroll))
    || graph.edges.some((edge) => !ids.has(edge.from) || !ids.has(edge.to))) {
    throw new Error("Invalid node IDs, locations, or edge references.");
  }
  return graph;
}

function positions(graph: AliveGraph | null) {
  const levels = new Map<string, number>();
  const incoming = new Map<string, number>();
  const outgoing = new Map<string, string[]>();
  for (const node of graph?.nodes ?? []) { levels.set(node.id, 0); incoming.set(node.id, 0); }
  for (const edge of graph?.edges ?? []) {
    incoming.set(edge.to, (incoming.get(edge.to) ?? 0) + 1);
    outgoing.set(edge.from, [...(outgoing.get(edge.from) ?? []), edge.to]);
  }
  const queue = [...incoming.keys()].filter((id) => incoming.get(id) === 0);
  for (let i = 0; i < queue.length; ++i) {
    const id = queue[i];
    for (const to of outgoing.get(id) ?? []) {
      levels.set(to, Math.max(levels.get(to) ?? 0, (levels.get(id) ?? 0) + 1));
      incoming.set(to, incoming.get(to)! - 1);
      if (incoming.get(to) === 0) queue.push(to);
    }
  }
  const rows = new Map<number, string[]>();
  for (const node of graph?.nodes ?? []) {
    const level = levels.get(node.id) ?? 0;
    rows.set(level, [...(rows.get(level) ?? []), node.id]);
  }
  const width = Math.max(600, ...[...rows.values()].map((row) => row.length * 230));
  const points = new Map<string, { x: number; y: number }>();
  for (const [row, ids] of rows) ids.forEach((id, col) => points.set(id, { x: (width - ids.length * 230) / 2 + col * 230 + 25, y: row * 95 + 25 }));
  return { points, width, height: (Math.max(0, ...rows.keys()) + 1) * 95 + 25 };
}

function termText(term: AliveTerm | undefined) {
  if (!term) return "missing term";
  return `${term.id}: ${term.symbol ?? term.digits ?? term.op}${term.args.length ? `(${term.args.join(", ")})` : ""} : ${term.sort.kind}${term.sort.width ? term.sort.width : ""}`;
}

export function Alive2Page() {
  const [ir, setIr] = useState(SAMPLE);
  const [initial, setInitial] = useState('{"inputs":[{"name":"%x","type":"i64","kind":"symbolic"}]}');
  const [unroll, setUnroll] = useState(2);
  const [graph, setGraph] = useState<AliveGraph | null>(null);
  const [picked, setPicked] = useState<string | null>(null);
  const [pickedEdge, setPickedEdge] = useState<string | null>(null);
  const [error, setError] = useState("");
  const [busy, setBusy] = useState(false);
  const layout = useMemo(() => positions(graph), [graph]);
  const termIndex = useMemo(() => new Map(graph?.terms?.map((term) => [term.id, term]) ?? []), [graph]);
  const node = graph ? selectedNode(graph, picked) : null;
  const edge = graph?.edges.find((item) => item.id === pickedEdge);
  function load(text: string) {
    const next = readGraph(text);
    setGraph(next); setPicked(next.nodes[0]?.id ?? null); setPickedEdge(null); setError("");
  }
  async function createRun() {
    setError(""); setBusy(true);
    try {
      const created = await fetch("/api/alive2/runs", { method: "POST", headers: { "content-type": "application/json" }, body: JSON.stringify({ ir_text: ir, initial: JSON.parse(initial), unroll_bound: unroll }) });
      if (!created.ok) throw new Error(await created.text());
      const body = await created.json() as { id: string };
      const loaded = await fetch(`/api/alive2/runs/${body.id}/graph`);
      if (!loaded.ok) throw new Error(await loaded.text());
      load(await loaded.text());
    } catch (reason) { setError(String(reason)); } finally { setBusy(false); }
  }
  return <div className="alive2">
    <style>{`
      .alive2 { height:100vh; display:flex; flex-direction:column; color:var(--text,#222); }
      .alive2 header, .alive2 .bar { padding:12px 16px; border-bottom:1px solid #ccc; display:flex; align-items:center; gap:12px; flex-wrap:wrap; }
      .alive2 h1 { font-size:18px; margin:0; }
      .alive2 .columns { flex:1; display:grid; grid-template-columns:280px minmax(360px,1fr) minmax(340px,420px); min-height:0; }
      .alive2 aside, .alive2 main { overflow:auto; border-right:1px solid #ccc; padding:12px; }
      .alive2 textarea { width:100%; box-sizing:border-box; font-family:monospace; }
      .alive2 pre { white-space:pre-wrap; overflow-wrap:anywhere; font-size:12px; }
      .alive2 label { display:block; margin-bottom:8px; }
      .alive2 svg { font:12px monospace; }
      .alive2 .selected rect { stroke:#176bc1; stroke-width:3; }
      .alive2 .error { color:#a52626; }
      .alive2 .edge-list button { display:block; width:100%; text-align:left; margin-bottom:4px; }
      @media(max-width:1000px) { .alive2 .columns { display:block; overflow:auto; } .alive2 main { height:55vh; } }
    `}</style>
    <header><h1>Alive2 状态推演</h1><span>原生 State 快照 · Rocq 对应单独标注</span></header>
    <div className="bar">
      <label>导入已保存 JSON <input type="file" accept=".json,application/json" onChange={(event) => { const file = event.target.files?.[0]; if (file) void file.text().then(load).catch((reason) => setError(String(reason))); }} /></label>
      <span>{graph ? `${graph.nodes[0]?.location.function} · ${graph.nodes.length} nodes · ${graph.edges.length} edges · ${graph.run.status} · truncation ${graph.run.truncation.kind}` : "导入 CLI 输出，或在左侧运行程序"}</span>
      <span>输入覆盖：{graph?.coverage.all_inputs_covered ?? "not_established"}</span>
    </div>
    {error && <p role="alert" className="error">{error}</p>}
    <div className="columns">
      <aside>
        <label>新建运行：Alive2 IR<textarea aria-label="Alive2 IR" value={ir} onChange={(e) => setIr(e.target.value)} rows={19} /></label>
        <label>Initial JSON<textarea aria-label="Initial JSON" value={initial} onChange={(e) => setInitial(e.target.value)} rows={5} /></label>
        <label>Unroll <input type="number" min="1" value={unroll} onChange={(e) => setUnroll(Number(e.target.value))} /></label>
        <button disabled={busy} onClick={() => void createRun()}>{busy ? "执行中…" : "运行"}</button>
        <p>左侧输入仅用于新建运行，与导入图独立。JSON 可独立查看；执行需要已配置的 Explorer。符号结果不等于可靠性证明。</p>
        <details className="edge-list"><summary>迁移边（点击查看 Guard 和变化）</summary>{graph?.edges.map((item) => <button key={item.id} onClick={() => setPickedEdge(item.id)}>{item.id} {item.from} → {item.to} {item.kind}</button>)}</details>
      </aside>
      <main aria-label="状态迁移图">
        <svg width={layout.width} height={layout.height} role="img" aria-label="Alive2 state graph">
          <defs><marker id="alive-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 0 0 L 10 5 L 0 10 z" fill="#777" /></marker></defs>
          {graph?.edges.map((item) => {
            const from = layout.points.get(item.from)!, to = layout.points.get(item.to)!;
            const path = `M ${from.x + 90} ${from.y + 48} C ${from.x + 90} ${from.y + 74}, ${to.x + 90} ${to.y - 24}, ${to.x + 90} ${to.y}`;
            const color = item.kind === "boundary" ? "#b45f06" : item.kind === "taken" ? "#16834e" : item.kind === "not_taken" ? "#9652a5" : "#777";
            return <g key={item.id} onClick={() => setPickedEdge(item.id)} style={{ cursor:"pointer" }}><title>{item.id} {item.kind} · {termText(termIndex.get(item.guard))}</title><path d={path} fill="none" stroke="transparent" strokeWidth="16" /><path d={path} fill="none" stroke={pickedEdge === item.id ? "#176bc1" : color} strokeWidth={pickedEdge === item.id ? 3 : 1.5} markerEnd="url(#alive-arrow)" /><text x={(from.x + to.x) / 2 + 96} y={from.y + 68} fill={color}>{item.kind} · {item.guard}</text></g>;
          })}
          {graph?.nodes.map((item) => { const point = layout.points.get(item.id)!; return <g key={item.id} transform={`translate(${point.x},${point.y})`} className={node?.id === item.id ? "selected" : ""} role="button" tabIndex={0} aria-label={`node ${item.id} ${item.location.block} ${item.state}`} onClick={() => { setPicked(item.id); setPickedEdge(null); }} onKeyDown={(e) => { if (e.key === "Enter") { setPicked(item.id); setPickedEdge(null); } }} style={{ cursor:"pointer" }}><rect width="180" height="48" rx="3" fill={item.state === "exit" ? "#e4f3e9" : item.state.includes("truncated") ? "#fff0d8" : item.state === "ub" ? "#ffe2e2" : "#f5f5f5"} stroke="#999" /><text x="8" y="19">{item.id} {item.location.block}</text><text x="8" y="37">u{item.unroll} · {item.state}</text></g>; })}
        </svg>
      </main>
      <aside aria-label="状态详情">
        {edge ? <><h2>Edge {edge.id}</h2><p>{edge.kind}: {edge.from} → {edge.to}</p><p>Guard {termText(termIndex.get(edge.guard))}</p><pre>{JSON.stringify(edge, null, 2)}</pre></> : node ? <><h2>Node {node.id}</h2><p>{node.location.block} · unroll {node.unroll} · {node.state}</p><p>累计路径 {termText(termIndex.get(node.path_condition ?? ""))}</p><h3>Alive2 State</h3><pre>{JSON.stringify(node.ir_state, null, 2)}</pre><h3>Rocq eBPF State</h3><p>{node.rocq_mapping?.status ?? "unsupported"}: {node.rocq_mapping?.reason ?? "无有效的完整状态对应"}</p><pre>{JSON.stringify(node.rocq_ebpf ?? null, null, 2)}</pre><details><summary>Origin / 完整节点</summary><pre>{JSON.stringify(node, null, 2)}</pre></details></> : <p>选择节点或边</p>}
        <details><summary>Memory 对象（原生编码）</summary><pre>{JSON.stringify(graph?.memories, null, 2)}</pre></details>
        <details><summary>Typed expression DAG</summary>{graph?.terms?.map((term) => <pre key={term.id}>{termText(term)}{term.unsupported ? ` unsupported: ${term.unsupported}` : ""}</pre>)}</details>
        <details><summary>Coverage / Evidence</summary><pre>{JSON.stringify({ coverage:graph?.coverage, evidence:graph?.evidence }, null, 2)}</pre></details>
      </aside>
    </div>
  </div>;
}
