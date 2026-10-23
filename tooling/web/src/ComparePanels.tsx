import { Box, Flex, Text } from "@kuma-ui/core";
import {
  formatEntryLine,
  predsFromSide,
  summarizeTreeNode,
  type AlignRow,
} from "./compareNodeSummary";
import { formatPredChip } from "./formatExpr";
import {
  atomToPred,
  type ListEntry,
  type SessionSnapshot,
  type TreeNode,
  type TreeReport,
} from "./types";
import { formatPred } from "./viewer";

type DetailSide = "left" | "right";

type Provenance = {
  left: SessionSnapshot;
  right: SessionSnapshot;
};

type SummaryProps = {
  report: TreeReport;
  node: TreeNode | null;
  provenance?: Provenance;
};

function verdictLabel(v: "same" | "diff" | "coverage"): string {
  if (v === "same") return "当前条目 fingerprint 对齐一致";
  if (v === "diff") return "双方均有独有条目";
  return "覆盖不全（仅一侧有额外条目）";
}

function statusText(snap: SessionSnapshot): string {
  if (snap.status === "complete") return "完成";
  if (snap.status === "fail") return "部分结果";
  return "进行中";
}

function formatFieldValue(value: unknown): string {
  if (typeof value === "string") return value;
  if (typeof value === "number" || typeof value === "boolean" || value == null) {
    return String(value);
  }
  return JSON.stringify(value);
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

function ProvenanceBlock({ snap, side }: { snap: SessionSnapshot; side: string }) {
  const partial = snap.status === "fail";
  return (
    <Text className="mono muted" display="block" fontSize={11} style={{ marginTop: 4 }}>
      {side} · {snap.program} · budget {snap.budget} · {statusText(snap)}
      {partial && snap.reason ? ` · ${snap.reason}` : ""}
    </Text>
  );
}

export function CompareSummaryPanel({ report, node, provenance }: SummaryProps) {
  const summary = node ? summarizeTreeNode(node) : null;
  return (
    <Flex className="panel panel--left" width={300} flexDirection="column" minHeight={0}>
      <Text className="panel__title">对比摘要</Text>
      <Box className="panel__body" flex="1" overflow="auto" minHeight={0} px={12} pb={10}>
        <Text className="mono muted" display="block" fontSize={11}>
          claim={report.claim} · phase={report.phase}
        </Text>
        {provenance ? (
          <>
            <ProvenanceBlock snap={provenance.left} side={`L · ${report.left.arch}`} />
            <ProvenanceBlock snap={provenance.right} side={`R · ${report.right.arch}`} />
          </>
        ) : (
          <Text className="mono muted" display="block" fontSize={11} style={{ marginTop: 4 }}>
            {report.left.arch} {report.left.expandNodes} 展开节点 / {report.left.segments} 分段 ·{" "}
            {report.right.arch} {report.right.expandNodes} 展开节点 / {report.right.segments} 分段
          </Text>
        )}
        <Text className="muted" display="block" fontSize={11} style={{ marginTop: 6 }}>
          仅 branch/ret 阶段；不代表行为等价。Term equality not proven.
        </Text>

        {!summary ? (
          <Text className="muted" display="block" style={{ marginTop: 16 }}>
            选择树节点查看详情
          </Text>
        ) : (
          <>
            <Text className="sem-heading" style={{ marginTop: 14 }}>
              #{summary.id} · {summary.start}
            </Text>
            <div className={`compare-row compare-row--${summary.verdict}`} style={{ marginTop: 8 }}>
              <div className="compare-row__head" style={{ cursor: "default" }}>
                <span className="compare-row__verdict mono">{verdictLabel(summary.verdict)}</span>
              </div>
              <Text className="mono muted" display="block" fontSize={11} style={{ marginTop: 4 }}>
                双方对齐条目 {summary.both} · 仅左 {summary.onlyLeft} · 仅右 {summary.onlyRight}
              </Text>
            </div>

            {summary.tipScore ? (
              <Box style={{ marginTop: 10 }}>
                <Text className="panel__title panel__title--small">分支末端启发式相似度</Text>
                <Text className="mono" display="block" fontSize={11}>
                  overall {(summary.tipScore.overall * 100).toFixed(0)}% · kind{" "}
                  {(summary.tipScore.kind * 100).toFixed(0)}% · fields{" "}
                  {(summary.tipScore.fields * 100).toFixed(0)}% · terms{" "}
                  {(summary.tipScore.terms * 100).toFixed(0)}%
                </Text>
              </Box>
            ) : null}

            <Box style={{ marginTop: 12 }}>
              <Text className="panel__title panel__title--small">本节点含 exit</Text>
              <Text className="mono" display="block" fontSize={11}>
                {report.left.arch} {summary.leftExit ? "有" : "无"} · {report.right.arch}{" "}
                {summary.rightExit ? "有" : "无"}
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

function FieldList({ fields }: { fields: Record<string, unknown> }) {
  const keys = Object.keys(fields);
  if (keys.length === 0) {
    return (
      <Text className="mono muted" display="block" fontSize={10}>
        （无 fields）
      </Text>
    );
  }
  return (
    <div className="compare-fields">
      {keys.map((k) => (
        <div key={k} className="compare-fields__row">
          <span className="mono compare-fields__key">{k}</span>
          <span className="mono compare-fields__val">{formatFieldValue(fields[k])}</span>
        </div>
      ))}
    </div>
  );
}

function EntryDetail({ entry }: { entry: ListEntry }) {
  if (entry.tag === "exit") {
    return (
      <Text className="mono" display="block" fontSize={12} style={{ marginBottom: 8 }}>
        exit
      </Text>
    );
  }
  const row = atomToPred(entry.atom);
  return (
    <div className="compare-entry" style={{ marginBottom: 10 }}>
      <div className="capsule-row" style={{ marginBottom: 4 }}>
        <span className="capsule" title={formatPred(row)}>
          {formatPredChip(row)}
        </span>
      </div>
      <Text className="mono muted" display="block" fontSize={10}>
        #{entry.atom.node_id} · loc {entry.atom.loc} · {entry.atom.kind}
      </Text>
      <FieldList fields={entry.atom.fields} />
    </div>
  );
}

export function CompareDetailPanel({ report, node, side, onSide }: DetailProps) {
  const entries = node ? predsFromSide(node, side) : [];
  const arch = side === "left" ? report.left.arch : report.right.arch;
  const missingSide = node != null && entries.length === 0;
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
            aria-pressed={side === id}
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
          <Text className="muted">选择树节点查看详情</Text>
        ) : missingSide ? (
          <Text className="muted">此节点无 {arch} 对应列表</Text>
        ) : (
          <>
            <Text className="sem-heading">
              #{node.id} · {arch} · {node.start}
            </Text>
            <Text className="mono muted" display="block" fontSize={11} style={{ marginBottom: 10 }}>
              {entries.length} 条
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
