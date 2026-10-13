import { Box, Flex, Text } from "@kuma-ui/core";
import { useMemo, useState } from "react";
import { formatPredChip } from "./formatExpr";
import {
  atomToPred,
  type PredAtom,
  type PredMatchReport,
  type PredPair,
} from "./types";
import { formatPred } from "./viewer";

export type PredFilter = "all" | "matched" | "only-left" | "only-right";

function pairPasses(p: PredPair, filter: PredFilter): boolean {
  if (filter === "all") return true;
  if (filter === "matched") return p.status === "matched";
  if (filter === "only-left") return p.status === "onlyLeft";
  return p.status === "onlyRight";
}

function PredChip({ atom }: { atom: PredAtom }) {
  const row = atomToPred(atom);
  return (
    <span
      className={`capsule capsule--pred capsule--${row.kind}`}
      title={`#${atom.node_id} · ${formatPred(row)}`}
    >
      {formatPredChip(row)}
    </span>
  );
}

function ScoreBar({ overall }: { overall: number }) {
  const pct = Math.round(Math.max(0, Math.min(1, overall)) * 100);
  return (
    <div className="pred-score" title={`overall ${overall.toFixed(2)}`}>
      <div className="pred-score__track">
        <div className="pred-score__fill" style={{ width: `${pct}%` }} />
      </div>
      <span className="mono muted pred-score__pct">{pct}%</span>
    </div>
  );
}

type Props = {
  report: PredMatchReport;
};

export function PredicateCompareView({ report }: Props) {
  const [filter, setFilter] = useState<PredFilter>("all");

  const locs = useMemo(() => {
    return report.locations
      .map((bucket) => ({
        ...bucket,
        pairs: bucket.pairs.filter((p) => pairPasses(p, filter)),
      }))
      .filter((b) => b.pairs.length > 0);
  }, [report, filter]);

  return (
    <Flex className="pred-compare panel" flex="1" flexDirection="column" minHeight={0} minWidth={0}>
      <Box className="pred-compare__header" px={14} pt={12} pb={10}>
        <Text className="pred-compare__title" display="block">
          claim={report.claim} · behavioralEquivalence={report.behavioralEquivalence}
        </Text>
        <Text className="mono muted" display="block" fontSize={12} style={{ marginTop: 4 }}>
          matched {report.matched} · onlyLeft {report.only_left} · onlyRight{" "}
          {report.only_right} · {report.left.arch} {report.left.predCount} preds ·{" "}
          {report.right.arch} {report.right.predCount} preds
        </Text>
        <Text className="muted" display="block" fontSize={11} style={{ marginTop: 6 }}>
          {report.note}. Term equality is not proven.
        </Text>
        <Flex gap={6} flexWrap="wrap" style={{ marginTop: 10 }}>
          {(
            [
              ["all", "全部"],
              ["matched", "matched"],
              ["only-left", "only-left"],
              ["only-right", "only-right"],
            ] as const
          ).map(([id, label]) => (
            <button
              key={id}
              type="button"
              className={`compare-filter${filter === id ? " compare-filter--on" : ""}`}
              onClick={() => setFilter(id)}
            >
              {label}
            </button>
          ))}
        </Flex>
      </Box>

      <Box className="pred-compare__body" flex="1" overflow="auto" px={12} pb={12} minHeight={0}>
        {locs.length === 0 ? (
          <Text className="muted">无 Predicate 观测（或当前过滤为空）</Text>
        ) : null}
        {locs.map((bucket) => (
          <Box key={bucket.loc} className="pred-loc" style={{ marginBottom: 10 }}>
            <Text className="pred-loc__title mono">
              loc {bucket.loc === "exit" ? "exit" : bucket.loc}
              <span className="muted">
                {" "}
                · L{bucket.leftCount} / R{bucket.rightCount}
              </span>
            </Text>
            {bucket.pairs.map((pair, i) => (
              <Box
                key={`${bucket.loc}:${pair.status}:${i}`}
                className={`pred-pair pred-pair--${pair.status}`}
              >
                {pair.status === "matched" ? (
                  <>
                    <Flex className="pred-pair__row" gap={10} alignItems="center">
                      <span className="pred-pair__side mono muted">L</span>
                      <PredChip atom={pair.left} />
                      <span className="pred-pair__side mono muted">R</span>
                      <PredChip atom={pair.right} />
                      <ScoreBar overall={pair.score.overall} />
                    </Flex>
                  </>
                ) : null}
                {pair.status === "onlyLeft" ? (
                  <Flex className="pred-pair__row" gap={10} alignItems="center">
                    <span className="pred-pair__badge mono">only-left</span>
                    <PredChip atom={pair.left} />
                  </Flex>
                ) : null}
                {pair.status === "onlyRight" ? (
                  <Flex className="pred-pair__row" gap={10} alignItems="center">
                    <span className="pred-pair__badge mono">only-right</span>
                    <PredChip atom={pair.right} />
                  </Flex>
                ) : null}
              </Box>
            ))}
          </Box>
        ))}
      </Box>
    </Flex>
  );
}
