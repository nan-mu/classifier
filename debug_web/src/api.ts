import type { SessionSnapshot } from "./types";

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

export function createSession(budget = 11): Promise<SessionSnapshot> {
  return postJson("/api/session", { budget });
}

export function stepSession(id: string): Promise<SessionSnapshot> {
  return postJson(`/api/session/${id}/step`, {});
}

export function runSession(id: string): Promise<SessionSnapshot> {
  return postJson(`/api/session/${id}/run`, {});
}
