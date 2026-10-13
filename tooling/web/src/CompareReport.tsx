import { Box, Flex, Text } from "@kuma-ui/core";
import { useMemo, useState } from "react";
import { formatExprMath } from "./formatExpr";
import type {
  ClassMember,
  CompareReject,
  CompareReport as CompareReportBody,
  ExprRow,
  PositionReport,
  PredRow,
  SessionSnapshot,
} from "./types";
import { formatPred } from "./viewer";

export type LedgerFilter = "all" | "diff-only" | "coverage-only";

const CONCLUSION_ZH: Record<CompareReportBody["conclusion"], string> = {
  sameStructure: "结构相同",
  differs: "结构不同",
  coverageDiffers: "覆盖不同",
};

function isExprRow(m: ClassMember): m is ExprRow {
  return typeof m === "object" && m !== null && "reg" in m && "rel" in m && "term" in m;
}

function isPredRow(m: ClassMember): m is PredRow {
  return typeof m === "object" && m !== null && "kind" in m;
}

export function formatMember(m: ClassMember): string {
  if (typeof m === "string") return m;
  if (isExprRow(m)) return formatExprMath(m);
  if (isPredRow(m)) return formatPred(m);
  return JSON.stringify(m);
}

function rowTone(p: PositionReport): "same" | "diff" | "coverage" {
  if (p.verdict !== "Both") return "coverage";
  if (p.control?.verdict === "Differs") return "diff";
  if (p.classes?.some((c) => c.verdict !== "equal")) return "diff";
  return "same";
}

function passesFilter(p: PositionReport, filter: LedgerFilter): boolean {
  if (filter === "all") return true;
  const tone = rowTone(p);
  if (filter === "diff-only") return tone === "diff";
  return tone === "coverage";
}

type Props = {
  left: SessionSnapshot;
  right: SessionSnapshot;
  report?: CompareReportBody;
  reject?: CompareReject;
  openLoc: string | null;
  onOpenLoc: (loc: string | null) => void;
};

export function CompareReportView({
  left,
  right,
  report,
  reject,
  openLoc,
  onOpenLoc,
}: Props) {
  const [filter, setFilter] = useState<LedgerFilter>("all");

  const rows = useMemo(() => {
    if (!report) return [];
    return report.positions.filter((p) => passesFilter(p, filter));
  }, [report, filter]);

  return (
    <Flex className="compare-spine panel" flex="1" flexDirection="column" minHeight={0} minWidth={0}>
      <Box className="compare-spine__header" px={14} pt={12} pb={10}>
        {report ? (
          <>
            <Text className="compare-spine__conclusion mono" display="block">
              {report.conclusion}
              <span className="muted"> · {CONCLUSION_ZH[report.conclusion]}</span>
            </Text>
            <Text className="mono muted" display="block" fontSize={12}>
              claim={report.claim} · 结构声明
            </Text>
            <Text className="mono muted" display="block" fontSize={12}>
              behavioralEquivalence={report.behavioralEquivalence} · 未建立行为等价
            </Text>
            <Text className="mono muted" display="block" fontSize={11} mt={6}>
              left {report.left.arch} nodes={report.left.nodeCount} edges={report.left.edgeCount}
              {" · "}
              status={left.status}
              {left.reason ? ` ${left.reason}` : ""}
            </Text>
            <Text className="mono muted" display="block" fontSize={11}>
              right {report.right.arch} nodes={report.right.nodeCount} edges={report.right.edgeCount}
              {" · "}
              status={right.status}
              {right.reason ? ` ${right.reason}` : ""}
            </Text>
          </>
        ) : reject ? (
          <>
            <Text className="compare-spine__conclusion mono" display="block">
              reject
            </Text>
            <Text className="mono" display="block" fontSize={13}>
              {reject.reason}
            </Text>
            <Text className="mono muted" display="block" fontSize={12} mt={4}>
              {reject.detail}
            </Text>
            <Text className="mono muted" display="block" fontSize={11} mt={6}>
              left {left.arch} status={left.status}
              {left.reason ? ` ${left.reason}` : ""} · nodes={left.nodes.length}
            </Text>
            <Text className="mono muted" display="block" fontSize={11}>
              right {right.arch} status={right.status}
              {right.reason ? ` ${right.reason}` : ""} · nodes={right.nodes.length}
            </Text>
          </>
        ) : null}

        {report ? (
          <Flex className="compare-spine__filters" gap={6} mt={10}>
            {(
              [
                ["all", "全部"],
                ["diff-only", "仅差异"],
                ["coverage-only", "仅覆盖"],
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
        ) : null}
      </Box>

      {report ? (
        <Box className="compare-spine__rows" flex="1" overflow="auto" minHeight={0} px={10} pb={12}>
          {rows.map((p) => {
            const open = openLoc === p.loc;
            const tone = rowTone(p);
            return (
              <Box
                key={p.loc}
                className={`compare-row compare-row--${tone}${open ? " compare-row--open" : ""}`}
              >
                <button
                  type="button"
                  className="compare-row__head"
                  onClick={() => onOpenLoc(open ? null : p.loc)}
                >
                  <span className="mono compare-row__loc">{p.loc}</span>
                  <span className="mono compare-row__verdict">{p.verdict}</span>
                  <span className="mono muted">
                    L={p.leftNodes} R={p.rightNodes}
                  </span>
                </button>
                {open ? (
                  <Box className="compare-row__body" px={10} pb={10}>
                    {p.verdict === "Both" && p.control ? (
                      <>
                        <Text className="mono" display="block" fontSize={12}>
                          control {p.control.verdict}
                        </Text>
                        <MemberList label="membersLeft" items={p.control.membersLeft} />
                        <MemberList label="membersRight" items={p.control.membersRight} />
                        <MemberList label="onlyLeft" items={p.control.onlyLeft} />
                        <MemberList label="onlyRight" items={p.control.onlyRight} />
                      </>
                    ) : null}
                    {p.verdict === "Both" && p.classes
                      ? p.classes.map((c) => (
                          <Box key={c.class} className="compare-class" mt={8}>
                            <Text className="mono" display="block" fontSize={12}>
                              {c.class} · {c.verdict} · L={c.leftCount} R={c.rightCount}
                            </Text>
                            <MemberList label="onlyLeft" items={c.onlyLeft} />
                            <MemberList label="onlyRight" items={c.onlyRight} />
                          </Box>
                        ))
                      : null}
                    {p.verdict !== "Both" ? (
                      <Text className="mono muted" display="block" fontSize={11}>
                        覆盖侧无 control / classes
                      </Text>
                    ) : null}
                  </Box>
                ) : null}
              </Box>
            );
          })}

          <details className="compare-obligations">
            <summary className="mono muted">basis / openObligations</summary>
            <Text className="mono muted" display="block" fontSize={11} mt={6}>
              basis
            </Text>
            {report.basis.map((b, i) => (
              <Text key={`b-${i}`} className="mono" display="block" fontSize={11}>
                {b}
              </Text>
            ))}
            <Text className="mono muted" display="block" fontSize={11} mt={8}>
              openObligations
            </Text>
            {report.openObligations.map((o, i) => (
              <Text key={`o-${i}`} className="mono" display="block" fontSize={11}>
                {o}
              </Text>
            ))}
          </details>
        </Box>
      ) : null}
    </Flex>
  );
}

function MemberList({ label, items }: { label: string; items: ClassMember[] | string[] }) {
  if (items.length === 0) return null;
  return (
    <Box mt={4}>
      <Text className="mono muted" display="block" fontSize={11}>
        {label}
      </Text>
      {items.map((item, i) => (
        <Text key={i} className="mono compare-member" display="block" fontSize={11}>
          {typeof item === "string" ? item : formatMember(item)}
        </Text>
      ))}
    </Box>
  );
}
