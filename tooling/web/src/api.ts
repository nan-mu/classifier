import type { ArchKind, SessionSnapshot } from "./types";

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

export function runSession(id: string): Promise<SessionSnapshot> {
  return postJson(`/api/session/${id}/run`, {});
}
