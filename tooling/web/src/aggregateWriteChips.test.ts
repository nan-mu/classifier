import { describe, expect, it } from "vitest";
import { cardChips } from "./aggregateWriteChips";
import type { ListEntry, PredAtom } from "./types";

function pred(kind: string, fields: Record<string, unknown> = {}): ListEntry {
  const atom: PredAtom = {
    node_id: 1,
    loc: "57",
    index: 0,
    kind,
    fields,
    fingerprint: kind,
  };
  return { tag: "pred", atom };
}

describe("cardChips", () => {
  it("drops start entries and keeps a branch chip", () => {
    const chips = cardChips([
      { tag: "start", kind: "taken" },
      pred("branch", { dir: "taken" }),
    ]);
    expect(chips).toEqual([{ tag: "entry", entry: pred("branch", { dir: "taken" }) }]);
  });

  it("collapses a consecutive mapWrite run into one chip without offsets", () => {
    const chips = cardChips([
      pred("mapWrite", { offset: 4, map: "rx" }),
      pred("mapWrite", { offset: 8, map: "rx" }),
      pred("mapWrite", { offset: 12, map: "rx" }),
    ]);
    expect(chips).toEqual([{ tag: "writes", kind: "mapWrite", count: 3 }]);
  });

  it("collapses a consecutive packetWrite run and leaves other kinds", () => {
    const chips = cardChips([
      pred("branch", { dir: "taken" }),
      pred("packet_write", { offset: 0 }),
      pred("packetWrite", { offset: 4 }),
      pred("helper", { helperId: 1 }),
      pred("mapWrite", { offset: 1 }),
    ]);
    expect(chips).toEqual([
      { tag: "entry", entry: pred("branch", { dir: "taken" }) },
      { tag: "writes", kind: "packetWrite", count: 2 },
      { tag: "entry", entry: pred("helper", { helperId: 1 }) },
      { tag: "entry", entry: pred("mapWrite", { offset: 1 }) },
    ]);
  });

  it("does not merge writes across a different kind", () => {
    const chips = cardChips([
      pred("mapWrite", { offset: 1 }),
      pred("branch", { dir: "notTaken" }),
      pred("mapWrite", { offset: 2 }),
    ]);
    expect(chips).toEqual([
      { tag: "entry", entry: pred("mapWrite", { offset: 1 }) },
      { tag: "entry", entry: pred("branch", { dir: "notTaken" }) },
      { tag: "entry", entry: pred("mapWrite", { offset: 2 }) },
    ]);
  });
});
