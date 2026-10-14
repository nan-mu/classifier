import { atomToPred, type ListEntry, type SoftScore, type TreeNode } from "./types";
import { formatPred } from "./viewer";

export type AlignRow =
  | { status: "both"; left: ListEntry; right: ListEntry }
  | { status: "onlyLeft"; left: ListEntry }
  | { status: "onlyRight"; right: ListEntry };

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

/** Ordered align of dual ListEntry sequences (fingerprint / start / exit keys). */
export function alignListEntries(left: ListEntry[], right: ListEntry[]): AlignRow[] {
  const out: AlignRow[] = [];
  let i = 0;
  let j = 0;
  while (i < left.length && j < right.length) {
    const lk = entryKey(left[i]!);
    const rk = entryKey(right[j]!);
    if (lk === rk) {
      out.push({ status: "both", left: left[i]!, right: right[j]! });
      i += 1;
      j += 1;
      continue;
    }
    const rightHasLeft = right.slice(j + 1).some((e) => entryKey(e) === lk);
    const leftHasRight = left.slice(i + 1).some((e) => entryKey(e) === rk);
    if (rightHasLeft && !leftHasRight) {
      out.push({ status: "onlyRight", right: right[j]! });
      j += 1;
    } else if (leftHasRight && !rightHasLeft) {
      out.push({ status: "onlyLeft", left: left[i]! });
      i += 1;
    } else if (rightHasLeft && leftHasRight) {
      out.push({ status: "onlyLeft", left: left[i]! });
      i += 1;
    } else {
      out.push({ status: "onlyLeft", left: left[i]! });
      out.push({ status: "onlyRight", right: right[j]! });
      i += 1;
      j += 1;
    }
  }
  while (i < left.length) {
    out.push({ status: "onlyLeft", left: left[i]! });
    i += 1;
  }
  while (j < right.length) {
    out.push({ status: "onlyRight", right: right[j]! });
    j += 1;
  }
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

export function formatEntryLine(entry: ListEntry): string {
  if (entry.tag === "start") return `start ${entry.kind}`;
  if (entry.tag === "exit") return "exit";
  return formatPred(atomToPred(entry.atom));
}

export function predsFromSide(node: TreeNode, side: "left" | "right"): ListEntry[] {
  return side === "left" ? node.left : node.right;
}
