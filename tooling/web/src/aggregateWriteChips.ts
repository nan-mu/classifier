import type { ListEntry } from "./types";

export type CardChip =
  | { tag: "entry"; entry: ListEntry }
  | { tag: "writes"; kind: "mapWrite" | "packetWrite"; count: number };

/** Identity stand-in. The card still emits one chip per list entry. */
export function cardChips(entries: ListEntry[]): CardChip[] {
  return entries.map((entry) => ({ tag: "entry", entry }));
}
