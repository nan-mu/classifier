import { parseReg, type RegKind } from "./parse";
import type { ExprRow, GraphEdge, GraphNode, InsnRow, PredRow } from "./types";
import { diffPredicates } from "./viewer";

/**
 * Visual role for CSS accent. Priority: control/predicates → insn class →
 * access target (reg kind) → plain.
 *
 * First-line chips (`tags`) are **arrival** predicates P_i only (delta vs parent),
 * plus structural markers (入口/出口/拒绝). Path history, P_g, and insn class do
 * not appear in the title.
 */
export type NodeRole =
  | "failed"
  | "exit"
  | "entry"
  | "ret"
  | "helper"
  | "merge"
  | "branch"
  | "arm_taken"
  | "arm_not_taken"
  | "packet"
  | "map"
  | "jump"
  | "alu"
  | "reg_packet"
  | "reg_map"
  | "reg_stack"
  | "reg_real"
  | "ready"
  | "plain";

export type NodeRoleInfo = {
  role: NodeRole;
  label: string;
  /** 节点类型 chips (first line) — from P_i / structural markers. */
  tags: string[];
  /** Stable key for same-type folding (= sorted tags). */
  nodeType: string;
  /** Load/store family: shared bottom wash + reg-kind accent. */
  accessFamily: boolean;
};

const ROLE_PRIORITY: NodeRole[] = [
  "failed",
  "exit",
  "entry",
  "ret",
  "helper",
  "merge",
  "branch",
  "arm_taken",
  "arm_not_taken",
  "packet",
  "map",
  "jump",
  "alu",
  "reg_packet",
  "reg_map",
  "reg_stack",
  "reg_real",
  "ready",
  "plain",
];

const ROLE_LABEL: Record<NodeRole, string> = {
  failed: "拒绝",
  exit: "出口",
  entry: "入口",
  ret: "Ret",
  helper: "Helper",
  merge: "合并",
  branch: "Branch",
  arm_taken: "Taken",
  arm_not_taken: "NotTaken",
  packet: "PacketWrite",
  map: "MapWrite",
  jump: "跳转",
  alu: "ALU",
  reg_packet: "Packet",
  reg_map: "Map",
  reg_stack: "Stack",
  reg_real: "Real",
  ready: "待扩",
  plain: "步进",
};

function predKind(p: PredRow): string {
  return String(p.kind ?? "");
}

function predDir(p: PredRow): string {
  const v = p.dir;
  return typeof v === "string" ? v : "";
}

/** Short first-line chip for one Predicate. */
export function predChip(p: PredRow): string | null {
  const k = predKind(p);
  if (k === "helper") return "Helper";
  if (k === "ret" || k === "return") return "Ret";
  if (k === "mapWrite" || k === "map_write") return "MapWrite";
  if (k === "packetWrite" || k === "packet_write") return "PacketWrite";
  if (k === "mapLookup" || k === "map_lookup") return "MapLookup";
  if (k === "branch") {
    const dir = predDir(p);
    if (dir === "taken") return "Taken";
    if (dir === "not_taken" || dir === "notTaken") return "NotTaken";
    return "Branch";
  }
  if (!k) return null;
  return k;
}

function roleFromPred(p: PredRow): NodeRole | null {
  const k = predKind(p);
  if (k === "helper") return "helper";
  if (k === "ret" || k === "return") return "ret";
  if (k === "mapWrite" || k === "map_write") return "map";
  if (k === "packetWrite" || k === "packet_write") return "packet";
  if (k === "mapLookup" || k === "map_lookup") return "map";
  if (k === "branch") {
    const dir = predDir(p);
    if (dir === "taken") return "arm_taken";
    if (dir === "not_taken" || dir === "notTaken") return "arm_not_taken";
    return "branch";
  }
  return null;
}

function pickRole(candidates: NodeRole[]): NodeRole {
  let best: NodeRole = "plain";
  let bestIdx = ROLE_PRIORITY.length;
  for (const r of candidates) {
    const i = ROLE_PRIORITY.indexOf(r);
    if (i >= 0 && i < bestIdx) {
      best = r;
      bestIdx = i;
    }
  }
  return best;
}

function tagRank(tag: string): number {
  const order = [
    "拒绝",
    "出口",
    "入口",
    "Ret",
    "Helper",
    "合并",
    "Branch",
    "Taken",
    "NotTaken",
    "PacketWrite",
    "MapWrite",
    "MapLookup",
    "跳转",
    "ALU",
    "Packet",
    "Map",
    "Stack",
    "Real",
    "待扩",
    "步进",
  ];
  const i = order.indexOf(tag);
  return i >= 0 ? i : 100;
}

export function isMemoryMnemonic(m: string): boolean {
  return /^(LB|LH|LW|LBU|LHU|SB|SH|SW|C_LW|C_SW|C_LWSP|C_SWSP|C_LD|C_SD|LD|SD|FLW|FSW)$/.test(
    m,
  );
}

function isJumpMnemonic(m: string): boolean {
  return /^(JAL|JALR|J|JR|C_J|C_JR|C_JAL|C_JALR|AUIPC)$/.test(m);
}

function isBranchMnemonic(m: string): boolean {
  return /^(BEQ|BNE|BLT|BGE|BLTU|BGEU|C_BEQZ|C_BNEZ)$/.test(m);
}

function isAluMnemonic(m: string): boolean {
  return /^(LUI|ADDI|ADD|SUB|AND|OR|XOR|SLL|SRL|SRA|SLLI|SRLI|SRAI|SLT|SLTU|SLTI|SLTIU|MUL|MULH|MULHSU|MULHU|DIV|DIVU|REM|REMU|C_LI|C_LUI|C_ADDI|C_ADDI16SP|C_ADDI4SPN|C_MV|C_ADD|C_AND|C_OR|C_XOR|C_SUB|C_SLLI|C_SRLI|C_SRAI|C_ANDI|ANDI|ORI|XORI)$/.test(
    m,
  );
}

/** Dominant Expr register kind → color role (one hue per RegKind). */
export function dominantRegRole(exprs: ExprRow[]): NodeRole | null {
  const counts: Partial<Record<RegKind, number>> = {};
  for (const row of exprs) {
    const kind = parseReg(row.reg).kind;
    if (kind === "unknown") continue;
    counts[kind] = (counts[kind] ?? 0) + 1;
  }
  let best: RegKind | null = null;
  let bestN = 0;
  for (const kind of ["packet", "map", "context", "stack", "real"] as const) {
    const n = counts[kind] ?? 0;
    if (n > bestN) {
      best = kind;
      bestN = n;
    }
  }
  if (!best) return null;
  if (best === "packet") return "reg_packet";
  if (best === "map") return "reg_map";
  // Context shares the stack wash for now (virtual cell accent).
  if (best === "stack" || best === "context") return "reg_stack";
  return "reg_real";
}

/** Predicates that arrive on this node (P_i), not the accumulated P_g. */
export function arrivalPredicates(node: GraphNode, nodes: GraphNode[]): PredRow[] {
  const parent = nodes.find((n) => node.preds.includes(n.id));
  if (!parent) return node.predicates;
  return diffPredicates(parent.predicates, node.predicates).added;
}

export function classifyNodeRole(input: {
  node: GraphNode;
  nodes?: GraphNode[];
  edges: GraphEdge[];
  insnText?: string;
  work?: readonly number[];
  failedId?: number | null;
}): NodeRoleInfo {
  const { node, edges, insnText, work, failedId } = input;
  const nodes = input.nodes ?? [node];
  const pi = arrivalPredicates(node, nodes);
  const roles: NodeRole[] = [];
  const tags: string[] = [];
  let accessFamily = false;

  const pushTag = (t: string) => {
    if (!tags.includes(t)) tags.push(t);
  };

  if (failedId != null && node.id === failedId) {
    roles.push("failed");
    pushTag(ROLE_LABEL.failed);
  }
  if (node.loc === "exit") {
    roles.push("exit");
    pushTag(ROLE_LABEL.exit);
  }
  if (node.id === 0) {
    roles.push("entry");
    pushTag(ROLE_LABEL.entry);
  }

  for (const p of pi) {
    const chip = predChip(p);
    if (chip) pushTag(chip);
    const r = roleFromPred(p);
    if (r) roles.push(r);
  }

  // Color hints below are not title chips (path / insn / E_g are historical or side).
  const inbound = edges.filter((e) => e.to === node.id);
  const outbound = edges.filter((e) => e.from === node.id);
  if (
    node.merge_reuse_from != null ||
    inbound.some((e) => e.dir === "reuse") ||
    outbound.some((e) => e.dir === "reuse")
  ) {
    roles.push("merge");
  }

  const outTaken = outbound.some((e) => e.dir === "taken");
  const outNotTaken = outbound.some((e) => e.dir === "not_taken");
  if (outTaken && outNotTaken) roles.push("branch");

  const inTaken = inbound.some((e) => e.dir === "taken");
  const inNotTaken = inbound.some((e) => e.dir === "not_taken");
  if (inTaken && !inNotTaken) roles.push("arm_taken");
  if (inNotTaken && !inTaken) roles.push("arm_not_taken");

  const mnemonic = insnMnemonic(insnText);
  if (isMemoryMnemonic(mnemonic)) {
    accessFamily = true;
    roles.push(dominantRegRole(node.exprs) ?? "reg_real");
  } else if (isJumpMnemonic(mnemonic)) {
    roles.push("jump");
  } else if (isBranchMnemonic(mnemonic)) {
    roles.push("branch");
  } else if (isAluMnemonic(mnemonic)) {
    roles.push("alu");
  }

  const regRole = dominantRegRole(node.exprs);
  if (regRole && !accessFamily) roles.push(regRole);

  if (work?.includes(node.id)) roles.push("ready");

  if (tags.length === 0) {
    roles.push("plain");
    pushTag(ROLE_LABEL.plain);
  }

  tags.sort((a, b) => tagRank(a) - tagRank(b));
  const role = pickRole(roles);
  const nodeType = tags.join("|");
  return {
    role,
    label: tags[0] ?? ROLE_LABEL[role],
    tags,
    nodeType,
    accessFamily,
  };
}

export function insnMnemonic(text: string | undefined): string {
  if (!text) return "";
  const parts = text.trim().split(/\s+/);
  if (parts.length === 0) return "";
  if (/^[0-9a-fA-F]+$/.test(parts[0]!) && parts.length > 1) {
    return parts[1]!.toUpperCase();
  }
  return parts[0]!.toUpperCase();
}

export function insnTextForNode(
  node: GraphNode,
  insns: InsnRow[],
): string | undefined {
  if (node.loc === "exit") return undefined;
  const j = Number(node.loc);
  if (!Number.isFinite(j)) return undefined;
  return insns.find((row) => row.j === j)?.text;
}

export const NODE_ROLE_LEGEND: { role: NodeRole; label: string }[] = [
  { role: "entry", label: ROLE_LABEL.entry },
  { role: "exit", label: ROLE_LABEL.exit },
  { role: "branch", label: ROLE_LABEL.branch },
  { role: "arm_taken", label: ROLE_LABEL.arm_taken },
  { role: "arm_not_taken", label: ROLE_LABEL.arm_not_taken },
  { role: "merge", label: ROLE_LABEL.merge },
  { role: "helper", label: ROLE_LABEL.helper },
  { role: "ret", label: ROLE_LABEL.ret },
  { role: "packet", label: ROLE_LABEL.packet },
  { role: "map", label: ROLE_LABEL.map },
  { role: "jump", label: ROLE_LABEL.jump },
  { role: "alu", label: ROLE_LABEL.alu },
  { role: "reg_real", label: `${ROLE_LABEL.reg_real}（访存）` },
  { role: "reg_stack", label: `${ROLE_LABEL.reg_stack}（访存）` },
  { role: "reg_map", label: `${ROLE_LABEL.reg_map}（访存）` },
  { role: "reg_packet", label: `${ROLE_LABEL.reg_packet}（访存）` },
  { role: "ready", label: ROLE_LABEL.ready },
  { role: "failed", label: ROLE_LABEL.failed },
];
