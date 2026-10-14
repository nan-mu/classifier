import { atomToPred, type ListEntry, type SoftScore, type TreeNode } from "./types";
import { formatPred } from "./viewer";

export type AlignRow =
  | { status: "both"; left: ListEntry; right: ListEntry }
  | { status: "onlyLeft"; left: ListEntry }
  | { status: "onlyRight"; right: ListEntry };

export type MatchStatus = "pass" | "fail";

export type NodeDiffSummary = {
  id: number;
  start: TreeNode["start"];
  tipScore?: SoftScore;
  aligned: AlignRow[];
  both: number;
  onlyLeft: number;
  onlyRight: number;
  leftExit: boolean;
  rightExit: boolean;
  verdict: "same" | "diff" | "coverage";
};

function entryKey(entry: ListEntry): string {
  if (entry.tag === "start") return `start:${entry.kind}`;
  if (entry.tag === "exit") return "exit";
  return `pred:${entry.atom.fingerprint}`;
}

/**
 * Deterministic LCS on entryKey. On DP ties prefer onlyRight so a contiguous
 * left subsequence stays matched when right has an insert (see regression test).
 */
export function alignListEntries(left: ListEntry[], right: ListEntry[]): AlignRow[] {
  const n = left.length;
  const m = right.length;
  const dp: number[][] = Array.from({ length: n + 1 }, () => Array(m + 1).fill(0));
  for (let i = 1; i <= n; i++) {
    for (let j = 1; j <= m; j++) {
      if (entryKey(left[i - 1]!) === entryKey(right[j - 1]!)) {
        dp[i]![j] = dp[i - 1]![j - 1]! + 1;
      } else {
        dp[i]![j] = Math.max(dp[i - 1]![j]!, dp[i]![j - 1]!);
      }
    }
  }
  const out: AlignRow[] = [];
  let i = n;
  let j = m;
  while (i > 0 || j > 0) {
    if (i > 0 && j > 0 && entryKey(left[i - 1]!) === entryKey(right[j - 1]!)) {
      out.push({ status: "both", left: left[i - 1]!, right: right[j - 1]! });
      i -= 1;
      j -= 1;
    } else if (j > 0 && (i === 0 || dp[i]![j - 1]! >= dp[i - 1]![j]!)) {
      out.push({ status: "onlyRight", right: right[j - 1]! });
      j -= 1;
    } else {
      out.push({ status: "onlyLeft", left: left[i - 1]! });
      i -= 1;
    }
  }
  out.reverse();
  return out;
}

export function summarizeTreeNode(node: TreeNode): NodeDiffSummary {
  const aligned = alignListEntries(node.left, node.right);
  let both = 0;
  let onlyLeft = 0;
  let onlyRight = 0;
  for (const row of aligned) {
    if (row.status === "both") both += 1;
    else if (row.status === "onlyLeft") onlyLeft += 1;
    else onlyRight += 1;
  }
  const leftExit = node.left.some((e) => e.tag === "exit");
  const rightExit = node.right.some((e) => e.tag === "exit");
  let verdict: NodeDiffSummary["verdict"] = "same";
  if (onlyLeft > 0 && onlyRight > 0) verdict = "diff";
  else if (onlyLeft > 0 || onlyRight > 0 || leftExit !== rightExit) verdict = "coverage";
  return {
    id: node.id,
    start: node.start,
    tipScore: node.tipScore,
    aligned,
    both,
    onlyLeft,
    onlyRight,
    leftExit,
    rightExit,
    verdict,
  };
}

/** `same` is pass. `diff` and `coverage` are fail until the server sends `matchStatus`. */
export function matchStatusOf(node: TreeNode): MatchStatus {
  return summarizeTreeNode(node).verdict === "same" ? "pass" : "fail";
}

export function formatEntryLine(entry: ListEntry): string {
  if (entry.tag === "start") return `start ${entry.kind}`;
  if (entry.tag === "exit") return "exit";
  return formatPred(atomToPred(entry.atom));
}

export function predsFromSide(node: TreeNode, side: "left" | "right"): ListEntry[] {
  return side === "left" ? node.left : node.right;
}
