import type { ExprRow, GraphEdge, GraphNode, PredRow, SessionSnapshot } from "./types";

/** Local UI selection over an immutable Snapshot. Never mutates core SemState. */
export type ViewerSelection = {
  focus: number;
  compare: number | null;
  edgeKey: string | null;
  /** View-only: hide non-focused arrivals that share a program location. */
  collapseSameLoc: boolean;
  panel: "node" | "step" | "path" | "compare" | "dual";
};

export function edgeKey(e: Pick<GraphEdge, "from" | "to" | "dir">): string {
  return `${e.from}->${e.to}:${e.dir}`;
}

export function parseEdgeKey(key: string): { from: number; to: number; dir: string } | null {
  const m = /^(\d+)->(\d+):(.+)$/.exec(key);
  if (!m) return null;
  return { from: Number(m[1]), to: Number(m[2]), dir: m[3]! };
}

export function pathToRoot(nodeId: number, nodes: GraphNode[]): number[] {
  const byId = new Map(nodes.map((n) => [n.id, n]));
  const path: number[] = [];
  let cur: number | undefined = nodeId;
  const seen = new Set<number>();
  while (cur !== undefined && !seen.has(cur)) {
    seen.add(cur);
    path.push(cur);
    const n = byId.get(cur);
    if (!n || n.preds.length === 0) break;
    cur = n.preds[0];
  }
  return path.reverse();
}

/** Nodes already dequeued (not in Work and not Exit-pending). */
export function processedIds(snap: SessionSnapshot): Set<number> {
  const work = new Set(snap.work);
  const out = new Set<number>();
  for (const n of snap.nodes) {
    if (snap.status === "fail" && n.id === snap.failed) {
      out.add(n.id);
      continue;
    }
    if (work.has(n.id)) continue;
    if (n.loc === "exit") {
      out.add(n.id);
      continue;
    }
    // A non-work node that has been expanded has outgoing edges.
    if (snap.edges.some((e) => e.from === n.id)) out.add(n.id);
  }
  return out;
}

export function sameExprKey(a: ExprRow, b: ExprRow): boolean {
  return a.reg === b.reg && a.rel === b.rel && a.role === b.role
    && (a.role !== "constraint" || a.term === b.term);
}

export type ExprDiff = {
  added: ExprRow[];
  removed: ExprRow[];
  changed: { before: ExprRow; after: ExprRow }[];
  same: ExprRow[];
};

export function diffExprs(a: ExprRow[], b: ExprRow[]): ExprDiff {
  const added: ExprRow[] = [];
  const removed: ExprRow[] = [];
  const changed: { before: ExprRow; after: ExprRow }[] = [];
  const same: ExprRow[] = [];
  for (const be of b) {
    const ae = a.find((x) => sameExprKey(x, be));
    if (!ae) added.push(be);
    else if (ae.term !== be.term) changed.push({ before: ae, after: be });
    else same.push(be);
  }
  for (const ae of a) {
    if (!b.some((x) => sameExprKey(x, ae))) removed.push(ae);
  }
  return { added, removed, changed, same };
}

export const HELPER_NAMES: Record<number, string> = {
  1: "lookup",
  2: "update",
  3: "delete",
  5: "clock",
  6: "printk",
  28: "checksum",
  65: "adjustTail",
};

export function helperName(id: number | undefined): string {
  if (id == null) return "helper?";
  return HELPER_NAMES[id] ?? `helper${id}`;
}

function predStr(p: PredRow, key: string): string {
  const v = p[key];
  return typeof v === "string" ? v : v == null ? "" : String(v);
}

function predNum(p: PredRow, key: string): number | undefined {
  const v = p[key];
  return typeof v === "number" ? v : undefined;
}

function predArgs(p: PredRow): string[] {
  const v = p.args;
  return Array.isArray(v) ? v.map((x) => String(x)) : [];
}

function predKey(p: PredRow): string {
  if (p.kind === "ret" || p.kind === "return") return `ret:${predStr(p, "term")}`;
  if (p.kind === "helper") {
    return `helper:${predStr(p, "event")}:${predStr(p, "helperId")}:${predArgs(p).join(",")}`;
  }
  return `${p.kind}:${JSON.stringify(p)}`;
}

export function diffPredicates(a: PredRow[], b: PredRow[]): {
  added: PredRow[];
  removed: PredRow[];
} {
  const aKeys = new Set(a.map(predKey));
  const bKeys = new Set(b.map(predKey));
  return {
    added: b.filter((p) => !aKeys.has(predKey(p))),
    removed: a.filter((p) => !bKeys.has(predKey(p))),
  };
}

export function formatPred(p: PredRow): string {
  if (p.kind === "ret" || p.kind === "return") {
    return `ret ${predStr(p, "term") || "?"}`;
  }
  if (p.kind === "helper") {
    const name = helperName(predNum(p, "helperId"));
    const ev = predNum(p, "event") != null ? `@e${predNum(p, "event")}` : "";
    return `helper ${name}${ev}(${predArgs(p).join(", ")})`;
  }
  if (p.kind === "branch") {
    const at = predStr(p, "at") || predStr(p, "loc") || "?";
    return `branch ${predStr(p, "dir") || "?"} @${at}`;
  }
  if (p.kind === "mapWrite" || p.kind === "map_write") {
    const target = predStr(p, "addr") || predStr(p, "key") || predStr(p, "term");
    return target ? `map_write ${target}` : "map_write";
  }
  if (p.kind === "packetWrite" || p.kind === "packet_write") {
    const off = predStr(p, "offset") || predStr(p, "term");
    return off ? `packet_write ${off}` : "packet_write";
  }
  if (p.kind === "mapLookup" || p.kind === "map_lookup") {
    const target = predStr(p, "addr") || predStr(p, "key") || predStr(p, "term");
    return target ? `map_lookup ${target}` : "map_lookup";
  }
  return `${p.kind} predicate`;
}

export function countBranchEdges(snap: SessionSnapshot): {
  taken: number;
  notTaken: number;
} {
  let taken = 0;
  let notTaken = 0;
  for (const e of snap.edges) {
    if (e.dir === "taken") taken += 1;
    if (e.dir === "not_taken") notTaken += 1;
  }
  return { taken, notTaken };
}

/** Visible node ids under collapseSameLoc (data unchanged). */
export function visibleNodeIds(
  snap: SessionSnapshot,
  focus: number,
  compare: number | null,
  collapseSameLoc: boolean,
): Set<number> {
  if (!collapseSameLoc) return new Set(snap.nodes.map((n) => n.id));
  const keep = new Set<number>([focus]);
  if (compare !== null) keep.add(compare);
  if (snap.status === "fail" && snap.failed !== null) keep.add(snap.failed);
  const chosenLoc = new Map<string, number>();
  for (const n of snap.nodes) {
    if (keep.has(n.id)) {
      chosenLoc.set(n.loc, n.id);
    }
  }
  for (const n of snap.nodes) {
    const picked = chosenLoc.get(n.loc);
    if (picked === undefined) {
      chosenLoc.set(n.loc, n.id);
      keep.add(n.id);
    } else if (picked === n.id) {
      keep.add(n.id);
    }
  }
  // Always keep ancestors of focus so the path stays connected.
  for (const id of pathToRoot(focus, snap.nodes)) keep.add(id);
  if (compare !== null) {
    for (const id of pathToRoot(compare, snap.nodes)) keep.add(id);
  }
  if (snap.status === "fail" && snap.failed !== null) {
    for (const id of pathToRoot(snap.failed, snap.nodes)) keep.add(id);
  }
  return keep;
}

export function inboundEdges(nodeId: number, edges: GraphEdge[]): GraphEdge[] {
  return edges.filter((e) => e.to === nodeId);
}

export function outboundEdges(nodeId: number, edges: GraphEdge[]): GraphEdge[] {
  return edges.filter((e) => e.from === nodeId);
}

export function branchSource(focus: number, edges: GraphEdge[]): number | null {
  const branches = edges.filter((e) => e.dir === "taken" || e.dir === "not_taken");
  return (branches.find((e) => e.from === focus) ?? branches[0])?.from ?? null;
}
