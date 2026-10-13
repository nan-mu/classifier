import type {
  ArchKind,
  CompareOutcome,
  CompareRun,
  SessionSnapshot,
  TreeReport,
  TreeSnap,
} from "./types";

async function postJson(path: string, body: unknown): Promise<SessionSnapshot> {
  const res = await fetch(path, {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify(body),
  });
  if (!res.ok) {
    throw new Error(`${path} failed with ${res.status}`);
  }
  return (await res.json()) as SessionSnapshot;
}

export type CreateOpts = {
  budget?: number;
  arch?: ArchKind;
  name?: string;
  /** Compact XDP ELF bytes; omitted uses the embedded just_tx.elf. */
  image?: ArrayBuffer | null;
};

function bytesToBase64(buf: ArrayBuffer): string {
  const bytes = new Uint8Array(buf);
  let binary = "";
  const chunk = 0x8000;
  for (let i = 0; i < bytes.length; i += chunk) {
    binary += String.fromCharCode(...bytes.subarray(i, i + chunk));
  }
  return btoa(binary);
}

export function createSession(opts: CreateOpts = {}): Promise<SessionSnapshot> {
  const body: Record<string, unknown> = {
    budget: opts.budget ?? 1024,
    arch: opts.arch ?? "rv32imc",
    name: opts.name ?? "just_tx.elf",
  };
  if (opts.image && opts.image.byteLength > 0) {
    body.image_b64 = bytesToBase64(opts.image);
  }
  return postJson("/api/session", body);
}

export function stepSession(id: string): Promise<SessionSnapshot> {
  return postJson(`/api/session/${id}/step`, {});
}

/** Blocking run-to-end (tests / smoke). UI uses {@link runSessionStream}. */
export function runSession(id: string): Promise<SessionSnapshot> {
  return postJson(`/api/session/${id}/run`, {});
}

/** Structural same/diff. Lean `reject` is HTTP 200; pool/Lean errors are 5xx. */
export async function compareRuns(
  left: CompareRun,
  right: CompareRun,
): Promise<CompareOutcome> {
  const res = await fetch("/api/compare", {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify({ left, right }),
  });
  if (!res.ok) throw new Error(`/api/compare failed with ${res.status}`);
  const body = (await res.json()) as Partial<CompareOutcome>;
  if (body.status === "compared" || body.status === "reject") {
    return body as CompareOutcome;
  }
  throw new Error("unexpected compare status");
}

/** Compare tree of dual-list nodes (`claim: heuristic`). Phase1 branch/ret. */
export async function compareTree(
  left: TreeSnap,
  right: TreeSnap,
): Promise<TreeReport> {
  const res = await fetch("/api/compare/tree", {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify({ left, right }),
  });
  if (!res.ok) throw new Error(`/api/compare/tree failed with ${res.status}`);
  const body = (await res.json()) as Partial<TreeReport>;
  if (body.status === "tree" && body.claim === "heuristic") {
    return body as TreeReport;
  }
  throw new Error("unexpected compare-tree status");
}

export type RunStreamEvent = {
  kind: "step" | "done" | "error";
  elapsed_ms: number;
  steps: number;
  nodes: number;
  snapshot?: SessionSnapshot;
  message?: string;
};

export type RunStreamStats = {
  steps: number;
  nodes: number;
  elapsedMs: number;
  /** Expand steps per second from stream start. */
  stepsPerSec: number;
};

/**
 * Open a WebSocket and apply every expand tick until done/error/abort.
 * Resolves with the final snapshot (or rejects on transport/server error).
 */
export function runSessionStream(
  id: string,
  onTick: (snap: SessionSnapshot, stats: RunStreamStats) => void,
  signal?: AbortSignal,
): Promise<SessionSnapshot> {
  const proto = window.location.protocol === "https:" ? "wss:" : "ws:";
  const url = `${proto}//${window.location.host}/api/session/${encodeURIComponent(id)}/run/ws`;

  return new Promise((resolve, reject) => {
    const ws = new WebSocket(url);
    let settled = false;
    let last: SessionSnapshot | null = null;

    const fail = (err: Error) => {
      if (settled) return;
      settled = true;
      ws.close();
      reject(err);
    };

    const finish = (snap: SessionSnapshot) => {
      if (settled) return;
      settled = true;
      resolve(snap);
    };

    const onAbort = () => {
      ws.close();
      fail(new Error("run aborted"));
    };
    signal?.addEventListener("abort", onAbort, { once: true });

    ws.onmessage = (ev) => {
      let event: RunStreamEvent;
      try {
        event = JSON.parse(String(ev.data)) as RunStreamEvent;
      } catch {
        fail(new Error("invalid run event JSON"));
        return;
      }
      if (event.kind === "error") {
        fail(new Error(event.message ?? "run stream error"));
        return;
      }
      if (!event.snapshot) {
        fail(new Error("run event missing snapshot"));
        return;
      }
      last = event.snapshot;
      const elapsedMs = event.elapsed_ms;
      const stepsPerSec = elapsedMs > 0 ? (event.steps * 1000) / elapsedMs : 0;
      onTick(event.snapshot, {
        steps: event.steps,
        nodes: event.nodes,
        elapsedMs,
        stepsPerSec,
      });
      if (event.kind === "done") {
        settled = true;
        ws.close();
        resolve(event.snapshot);
      }
    };

    ws.onerror = () => fail(new Error("run websocket failed"));
    ws.onclose = () => {
      signal?.removeEventListener("abort", onAbort);
      if (!settled) {
        if (last) finish(last);
        else fail(new Error("run websocket closed"));
      }
    };
  });
}
