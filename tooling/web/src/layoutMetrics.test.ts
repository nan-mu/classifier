import { describe, expect, it } from "vitest";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import {
  buildDisplayGraph,
  layoutDisplay,
  measureLayout,
  segmentsCross,
} from "./layoutMetrics";
import type { SessionSnapshot } from "./types";

describe("segmentsCross", () => {
  it("detects an X crossing", () => {
    expect(
      segmentsCross(
        { id: "a", x1: 0, y1: 0, x2: 10, y2: 10 },
        { id: "b", x1: 0, y1: 10, x2: 10, y2: 0 },
      ),
    ).toBe(true);
  });

  it("ignores shared endpoints", () => {
    expect(
      segmentsCross(
        { id: "a", x1: 0, y1: 0, x2: 10, y2: 0 },
        { id: "b", x1: 10, y1: 0, x2: 20, y2: 0 },
      ),
    ).toBe(false);
  });
});

describe("measureLayout fixture", () => {
  it("reports zero stacks on single-shot fixture layout", () => {
    const snap = JSON.parse(
      readFileSync(resolve(__dirname, "__layout_fixture.json"), "utf8"),
    ) as SessionSnapshot;
    const display = buildDisplayGraph(snap);
    const pos = layoutDisplay(snap, display);
    const m = measureLayout(pos, display.edges);
    expect(m.stacks).toBe(0);
    expect(display.nodes.length).toBeGreaterThan(0);
    expect(m.multiYCols).toBeGreaterThan(0);
  });
});
