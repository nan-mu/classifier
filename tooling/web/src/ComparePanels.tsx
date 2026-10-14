import { Box, Flex, Text } from "@kuma-ui/core";
import {
  formatEntryLine,
  predsFromSide,
  summarizeTreeNode,
  type AlignRow,
} from "./compareNodeSummary";
import { formatPredChip } from "./formatExpr";
import { atomToPred, type ListEntry, type TreeNode, type TreeReport } from "./types";

type DetailSide = "left" | "right";

type SummaryProps = {
  report: TreeReport;
  node: TreeNode | null;
};

function verdictLabel(v: "same" | "diff" | "coverage"): string {
  if (v === "same") return "一致";
  if (v === "diff") return "双方差异";
  return "覆盖不全";
}

function AlignLine({ row, leftArch, rightArch }: { row: AlignRow; leftArch: string; rightArch: string }) {
  if (row.status === "both") {
    const sameText =
      formatEntryLine(row.left) === formatEntryLine(row.right)
        ? formatEntryLine(row.left)
        : `${formatEntryLine(row.left)} / ${formatEntryLine(row.right)}`;
    return (
      <Text className="mono compare-align compare-align--both" display="block" fontSize={11}>
        = {sameText}
      </Text>
    );
  }
  if (row.status === "onlyLeft") {
    return (
      <Text className="mono compare-align compare-align--left" display="block" fontSize={11}>
        − {leftArch} · {formatEntryLine(row.left)}
      </Text>
    );
  }
  return (
    <Text className="mono compare-align compare-align--right" display="block" fontSize={11}>
      + {rightArch} · {formatEntryLine(row.right)}
    </Text>
  );
}

export function CompareSummaryPanel({ report, node }: SummaryProps) {
  const summary = node ? summarizeTreeNode(node) : null;
  return (
    <Flex className="panel panel--left" width={300} flexDirection="column" minHeight={0}>
      <Text className="panel__title">对比摘要</Text>
      <Box className="panel__body" flex="1" overflow="auto" minHeight={0} px={12} pb={10}>
        <Text className="mono muted" display="block" fontSize={11}>
          claim={report.claim} · phase={report.phase}
        </Text>
        <Text className="mono muted" display="block" fontSize={11} style={{ marginTop: 4 }}>
          {report.left.arch} {report.left.expandNodes}n/{report.left.segments}s ·{" "}
          {report.right.arch} {report.right.expandNodes}n/{report.right.segments}s
        </Text>
        <Text className="muted" display="block" fontSize={11} style={{ marginTop: 6 }}>
          {report.note}. Term equality not proven.
        </Text>

        {!summary ? (
          <Text className="muted" display="block" style={{ marginTop: 16 }}>
            点击中间树节点查看结构化 diff。
          </Text>
        ) : (
          <>
            <Text className="sem-heading" style={{ marginTop: 14 }}>
              #{summary.id} · {summary.start}
            </Text>
            <div className={`compare-row compare-row--${summary.verdict}`} style={{ marginTop: 8 }}>
              <div className="compare-row__head" style={{ cursor: "default" }}>
                <span className="compare-row__verdict mono">{verdictLabel(summary.verdict)}</span>
                <span className="mono muted">
                  both {summary.both} · onlyL {summary.onlyLeft} · onlyR {summary.onlyRight}
                </span>
              </div>
            </div>

            {summary.tipScore ? (
              <Box style={{ marginTop: 10 }}>
                <Text className="panel__title panel__title--small">tipScore</Text>
                <Text className="mono" display="block" fontSize={11}>
                  overall {(summary.tipScore.overall * 100).toFixed(0)}% · kind{" "}
                  {(summary.tipScore.kind * 100).toFixed(0)}% · fields{" "}
                  {(summary.tipScore.fields * 100).toFixed(0)}% · terms{" "}
                  {(summary.tipScore.terms * 100).toFixed(0)}%
                </Text>
              </Box>
            ) : null}

            <Box style={{ marginTop: 12 }}>
              <Text className="panel__title panel__title--small">exit</Text>
              <Text className="mono" display="block" fontSize={11}>
                {report.left.arch} {summary.leftExit ? "yes" : "no"} · {report.right.arch}{" "}
                {summary.rightExit ? "yes" : "no"}
              </Text>
            </Box>

            <Box style={{ marginTop: 12 }}>
              <Text className="panel__title panel__title--small">序列对齐</Text>
              {summary.aligned.map((row, i) => (
                <AlignLine
                  key={i}
                  row={row}
                  leftArch={report.left.arch}
                  rightArch={report.right.arch}
                />
              ))}
            </Box>
          </>
        )}
      </Box>
    </Flex>
  );
}

type DetailProps = {
  report: TreeReport;
  node: TreeNode | null;
  side: DetailSide;
  onSide: (side: DetailSide) => void;
};

function EntryDetail({ entry }: { entry: ListEntry }) {
  if (entry.tag === "start") {
    return (
      <Text className="mono" display="block" fontSize={12}>
        start · {entry.kind}
      </Text>
    );
  }
  if (entry.tag === "exit") {
    return (
      <Text className="mono" display="block" fontSize={12}>
        exit
      </Text>
    );
  }
  const row = atomToPred(entry.atom);
  return (
    <div className="capsule-row" style={{ marginBottom: 6 }}>
      <span className="capsule" title={`#${entry.atom.node_id} @ ${entry.atom.loc}`}>
        {formatPredChip(row)}
      </span>
      <Text className="mono muted" display="block" fontSize={10}>
        #{entry.atom.node_id} · loc {entry.atom.loc} · {entry.atom.kind}
      </Text>
    </div>
  );
}

export function CompareDetailPanel({ report, node, side, onSide }: DetailProps) {
  const entries = node ? predsFromSide(node, side) : [];
  const arch = side === "left" ? report.left.arch : report.right.arch;
  return (
    <Flex className="panel panel--right" flexDirection="column" minHeight={0}>
      <Flex className="panel-tabs" gap={6} px={10} pt={8}>
        {(
          [
            ["left", report.left.arch],
            ["right", report.right.arch],
          ] as const
        ).map(([id, label]) => (
          <button
            key={id}
            type="button"
            className={`tab-btn${side === id ? " tab-btn--on" : ""}`}
            onClick={() => onSide(id)}
          >
            {label}
          </button>
        ))}
      </Flex>
      <Box
        className="panel__body panel__body--state"
        flex="1"
        overflow="auto"
        minHeight={0}
        px={12}
        pb={8}
      >
        {!node ? (
          <Text className="muted">等待节点…</Text>
        ) : (
          <>
            <Text className="sem-heading">
              #{node.id} · {arch} · {node.start}
            </Text>
            <Text className="mono muted" display="block" fontSize={11} style={{ marginBottom: 10 }}>
              {entries.length} entries
            </Text>
            {entries.map((entry, i) => (
              <EntryDetail key={i} entry={entry} />
            ))}
          </>
        )}
      </Box>
    </Flex>
  );
}
