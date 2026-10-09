import type { ProgramKind, SessionSnapshot } from "./types";

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
  program?: ProgramKind;
};

export function createSession(opts: CreateOpts = {}): Promise<SessionSnapshot> {
  return postJson("/api/session", {
    budget: opts.budget ?? 11,
    program: opts.program ?? "esp32c3",
  });
}

export function stepSession(id: string): Promise<SessionSnapshot> {
  return postJson(`/api/session/${id}/step`, {});
}

export function runSession(id: string): Promise<SessionSnapshot> {
  return postJson(`/api/session/${id}/run`, {});
}
