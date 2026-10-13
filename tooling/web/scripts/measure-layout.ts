/**
 * Measure edge crossings / node stacks after layout — no browser.
 *
 *   npm run measure-layout
 *   npm run measure-layout -- --live --budget 1024
 *   npm run measure-layout -- --pins   # also print old incremental-pin path
 */
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { GAP_X, GAP_Y, layoutGraph } from "../src/layout";
import {
  buildDisplayGraph,
  formatReport,
  layoutDisplay,
  layoutIncremental,
  measureLayout,
  type LayoutReport,
} from "../src/layoutMetrics";
import type { GraphEdge, SessionSnapshot } from "../src/types";

const API = process.env.EXPAND_API ?? "http://127.0.0.1:8788";

function arg(flag: string): string | undefined {
  const i = process.argv.indexOf(flag);
  if (i < 0) return undefined;
  return process.argv[i + 1];
}

function has(flag: string): boolean {
  return process.argv.includes(flag);
}

async function fetchLive(budget: number): Promise<SessionSnapshot> {
  const create = await fetch(`${API}/api/session`, {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify({
      budget,
      arch: "rv32imc",
      name: "just_tx.elf",
    }),
  });
  if (!create.ok) throw new Error(`create ${create.status}`);
  const snap0 = (await create.json()) as SessionSnapshot;
  const run = await fetch(`${API}/api/session/${snap0.id}/run`, {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: "{}",
  });
  if (!run.ok) throw new Error(`run ${run.status}`);
  return (await run.json()) as SessionSnapshot;
}

function loadFile(path: string): SessionSnapshot {
  return JSON.parse(readFileSync(path, "utf8")) as SessionSnapshot;
}

function pack(
  snap: SessionSnapshot,
  positions: ReturnType<typeof layoutGraph>,
  displayEdges: GraphEdge[],
  displayNodes: number,
): LayoutReport {
  const m = measureLayout(positions, displayEdges);
  return {
    nodes: snap.nodes.length,
    edges: snap.edges.length,
    displayNodes,
    displayEdges: displayEdges.length,
    gapX: GAP_X,
    gapY: GAP_Y,
    ...m,
  };
}

async function main() {
  let snap: SessionSnapshot;

  if (has("--live")) {
    const budget = Number(arg("--budget") ?? 1024);
    console.log(`live ${API} budget=${budget} …`);
    snap = await fetchLive(budget);
    console.log(
      `status=${snap.status} nodes=${snap.nodes.length} edges=${snap.edges.length}`,
    );
  } else {
    const file =
      arg("--file") ??
      resolve(import.meta.dirname, "../src/__layout_fixture.json");
    console.log(`file ${file}`);
    snap = loadFile(file);
  }

  const display = buildDisplayGraph(snap);

  console.log("\n=== display (UI path) ===");
  console.log(
    formatReport(
      pack(
        snap,
        layoutDisplay(snap, display),
        display.edges,
        display.nodes.length,
      ),
    ),
  );

  if (has("--pins")) {
    console.log("\n=== incremental pins (legacy A/B) ===");
    console.log(
      formatReport(
        pack(
          snap,
          layoutIncremental(display.nodes, display.edges),
          display.edges,
          display.nodes.length,
        ),
      ),
    );
  }
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
