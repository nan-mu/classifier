import type { ListEntry } from "./types";

export type WriteKind = "mapWrite" | "packetWrite";

export type CardChip =
  | { tag: "entry"; entry: ListEntry }
  | { tag: "writes"; kind: WriteKind; count: number };

function writeKind(entry: ListEntry): WriteKind | null {
  if (entry.tag !== "pred") return null;
  if (entry.atom.kind === "mapWrite" || entry.atom.kind === "packetWrite") {
    return entry.atom.kind;
  }
  return null;
}

export function cardChips(entries: ListEntry[]): CardChip[] {
  const out: CardChip[] = [];
  let run: { kind: WriteKind; entries: ListEntry[] } | null = null;

  const flush = () => {
    if (!run) return;
    const only = run.entries[0];
    if (run.entries.length === 1 && only) {
      out.push({ tag: "entry", entry: only });
    } else {
      out.push({ tag: "writes", kind: run.kind, count: run.entries.length });
    }
    run = null;
  };

  for (const entry of entries) {
    const kind = writeKind(entry);
    if (kind) {
      if (run && run.kind === kind) run.entries.push(entry);
      else {
        flush();
        run = { kind, entries: [entry] };
      }
      continue;
    }
    flush();
    out.push({ tag: "entry", entry });
  }
  flush();
  return out;
}
