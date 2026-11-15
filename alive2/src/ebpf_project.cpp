#include "ebpf_project.h"

#include "ebpf_concrete.h"
#include "smt/solver.h"
#include "smt/smt.h"

#include <cstdio>
#include <cerrno>
#include <cstring>
#include <iostream>
#include <optional>
#include <sstream>
#include <stdexcept>
#include <unistd.h>
#include <sys/wait.h>
#include <utility>

namespace {

const char *kProjection =
    "The Rocq side is a projection of the vendored instruction rules. "
    "It is not native Rocq symbolic execution. "
    "EQUIVALENT means the inequality is unsat under the assumption that each named input is not undef and not poison. "
    "An undef register can have definedness EQUIVALENT and value UNSUPPORTED. "
    "That UNSUPPORTED cell is not a pass.";

std::string json_escape(const std::string &text) {
  std::string out;
  out.reserve(text.size());
  for (unsigned char c : text) {
    switch (c) {
    case '\\': out += "\\\\"; break;
    case '"': out += "\\\""; break;
    case '\n': out += "\\n"; break;
    case '\r': out += "\\r"; break;
    case '\t': out += "\\t"; break;
    default:
      if (c < 0x20) {
        char buf[8];
        std::snprintf(buf, sizeof buf, "\\u%04x", c);
        out += buf;
      } else {
        out.push_back(static_cast<char>(c));
      }
    }
  }
  return out;
}

const char *verdict_name(Verdict verdict) {
  switch (verdict) {
  case Verdict::Equivalent: return "EQUIVALENT";
  case Verdict::Counterexample: return "COUNTEREXAMPLE";
  case Verdict::Unknown: return "UNKNOWN";
  case Verdict::Unsupported: return "UNSUPPORTED";
  }
  return "UNSUPPORTED";
}

const char *tag_name(CellTag tag) {
  switch (tag) {
  case CellTag::Input: return "input";
  case CellTag::Undef: return "undef";
  case CellTag::Zero: return "zero";
  case CellTag::Pointer: return "pointer";
  case CellTag::Bits: return "bits";
  }
  return "bits";
}

const char *kind_name(RNode::Kind kind) {
  switch (kind) {
  case RNode::Kind::Const: return "const";
  case RNode::Kind::Var: return "var";
  case RNode::Kind::Undef: return "undef";
  case RNode::Kind::Pointer: return "pointer";
  case RNode::Kind::Add: return "add";
  case RNode::Kind::Sub: return "sub";
  case RNode::Kind::Udiv: return "udiv";
  case RNode::Kind::Eq: return "eq";
  case RNode::Kind::Ugt: return "ugt";
  case RNode::Kind::Not: return "not";
  case RNode::Kind::And: return "and";
  case RNode::Kind::Or: return "or";
  case RNode::Kind::Ite: return "ite";
  case RNode::Kind::True: return "true";
  case RNode::Kind::False: return "false";
  }
  return "false";
}

RNode node_of(RNode::Kind kind, const char *cite) {
  RNode node;
  node.kind = kind;
  node.cite = cite;
  return node;
}

RNode bool_node(bool value, const char *cite) {
  return node_of(value ? RNode::Kind::True : RNode::Kind::False, cite);
}

RNode const_node(uint64_t imm, const char *cite) {
  RNode node = node_of(RNode::Kind::Const, cite);
  node.imm = imm;
  node.tag = imm == 0 ? CellTag::Zero : CellTag::Bits;
  return node;
}

RNode var_node(const std::string &name) {
  RNode node = node_of(RNode::Kind::Var, "Vlong");
  node.var = name;
  node.tag = CellTag::Input;
  return node;
}

RNode undef_node() {
  RNode node = node_of(RNode::Kind::Undef, "create_initial_state");
  node.tag = CellTag::Undef;
  return node;
}

RNode pointer_node() {
  RNode node = node_of(RNode::Kind::Pointer, "create_initial_state");
  node.tag = CellTag::Pointer;
  return node;
}

RNode wrap(RNode::Kind kind, const char *cite, RNode left, RNode right) {
  RNode node = node_of(kind, cite);
  node.tag = CellTag::Bits;
  node.kids = {std::move(left), std::move(right)};
  return node;
}

RNode lnot(RNode node, const char *cite) {
  if (node.kind == RNode::Kind::True)
    return bool_node(false, cite);
  if (node.kind == RNode::Kind::False)
    return bool_node(true, cite);
  RNode out = node_of(RNode::Kind::Not, cite);
  out.kids = {std::move(node)};
  return out;
}

RNode land(RNode left, RNode right, const char *cite) {
  if (left.kind == RNode::Kind::True)
    return right;
  if (right.kind == RNode::Kind::True)
    return left;
  if (left.kind == RNode::Kind::False || right.kind == RNode::Kind::False)
    return bool_node(false, cite);
  return wrap(RNode::Kind::And, cite, std::move(left), std::move(right));
}

RNode lor(RNode left, RNode right, const char *cite) {
  if (left.kind == RNode::Kind::False)
    return right;
  if (right.kind == RNode::Kind::False)
    return left;
  if (left.kind == RNode::Kind::True || right.kind == RNode::Kind::True)
    return bool_node(true, cite);
  return wrap(RNode::Kind::Or, cite, std::move(left), std::move(right));
}

bool same_node(const RNode &left, const RNode &right) {
  if (left.kind != right.kind || left.imm != right.imm || left.var != right.var ||
      left.kids.size() != right.kids.size())
    return false;
  for (size_t i = 0; i < left.kids.size(); ++i) {
    if (!same_node(left.kids[i], right.kids[i]))
      return false;
  }
  return true;
}

struct RReg {
  RNode node;
  CellTag tag = CellTag::Undef;
};

RReg reg_of(RNode node, CellTag tag) {
  node.tag = tag;
  return {std::move(node), tag};
}

uint64_t imm_bits(int32_t imm) {
  return static_cast<uint64_t>(static_cast<int64_t>(imm));
}

struct PEdge {
  int block = -1;
  int target_pc = -1;
  bool exit = false;
  RNode cond;
};

struct PBlock {
  int start = 0;
  int end = 0;
  std::vector<int> succ;
  std::vector<int> pred;
};

struct Sim {
  RNode path;
  std::array<RReg, 10> in{};
  std::array<RReg, 10> out{};
  std::vector<PEdge> edges;
  bool ready = false;
};

struct DraftPc {
  uint32_t pc = 0;
  std::string insn;
  std::vector<std::string> rules;
  RNode path;
  std::array<RReg, 10> pre{};
  std::array<RReg, 10> post{};
  std::vector<PEdge> edges;
  bool unsupported = false;
  bool pointer_use = false;
  std::string reason;
};

bool supported_insn(const EbInsn &insn) {
  if (const auto *alu = std::get_if<EbAlu>(&insn.op)) {
    if (alu->width != EbWidth::W64)
      return false;
    return alu->op == EbAlu::Mov || alu->op == EbAlu::Add ||
           alu->op == EbAlu::Sub || alu->op == EbAlu::Div;
  }
  const auto &jmp = std::get<EbJmp>(insn.op);
  if (jmp.op == EbJmp::Exit || jmp.op == EbJmp::Ja)
    return true;
  return jmp.op == EbJmp::Jgt && jmp.width == EbWidth::W64;
}

std::array<RReg, 10>
entry_regs(const std::vector<std::pair<uint8_t, std::string>> &inputs) {
  std::array<RReg, 10> regs;
  for (int i = 0; i < 10; ++i)
    regs[i] = reg_of(i == 1 ? pointer_node() : undef_node(),
                     i == 1 ? CellTag::Pointer : CellTag::Undef);
  for (auto [reg, name] : inputs) {
    if (reg > 9)
      throw std::runtime_error("input register out of range");
    regs[reg] = reg_of(var_node(name), CellTag::Input);
  }
  return regs;
}

RNode operand(const EbAlu &alu, const std::array<RReg, 10> &regs, bool &pointer) {
  if (alu.src == EbSrc::Reg) {
    if (regs[alu.src_reg].tag == CellTag::Pointer)
      pointer = true;
    return regs[alu.src_reg].node;
  }
  return const_node(imm_bits(alu.imm), "eval_alu64");
}

RReg eval_alu(const EbAlu &alu, const std::array<RReg, 10> &regs, bool &pointer,
              std::string &reason) {
  if (regs[alu.dst].tag == CellTag::Pointer)
    pointer = true;
  if (alu.src == EbSrc::Reg && regs[alu.src_reg].tag == CellTag::Pointer)
    pointer = true;
  if (pointer) {
    reason = "bitvector use of a pointer register";
    return reg_of(pointer_node(), CellTag::Pointer);
  }
  if (alu.op == EbAlu::Sub && alu.src == EbSrc::Reg && alu.src_reg == alu.dst)
    return reg_of(const_node(0, "exec_alu"), CellTag::Zero);
  auto src = operand(alu, regs, pointer);
  auto dst = regs[alu.dst];
  if (alu.op == EbAlu::Mov)
    return reg_of(src, src.tag);
  if (dst.tag == CellTag::Undef || src.tag == CellTag::Undef)
    return reg_of(undef_node(), CellTag::Undef);
  if (alu.op == EbAlu::Add)
    return reg_of(wrap(RNode::Kind::Add, "eval_alu64", dst.node, src), CellTag::Bits);
  if (alu.op == EbAlu::Sub)
    return reg_of(wrap(RNode::Kind::Sub, "eval_alu64", dst.node, src), CellTag::Bits);
  RNode src_for_div = src;
  RNode eq = wrap(RNode::Kind::Eq, "eval_div_u64", std::move(src),
                  const_node(0, "eval_div_u64"));
  RNode udiv = wrap(RNode::Kind::Udiv, "eval_div_u64", dst.node, std::move(src_for_div));
  RNode ite = node_of(RNode::Kind::Ite, "eval_div_u64");
  ite.tag = CellTag::Bits;
  ite.kids = {std::move(eq), const_node(0, "eval_div_u64"), std::move(udiv)};
  return reg_of(std::move(ite), CellTag::Bits);
}

RNode jgt_cond(const EbJmp &jmp, const std::array<RReg, 10> &regs, bool &pointer) {
  if (jmp.src == EbSrc::Reg && jmp.src_reg == jmp.dst)
    return bool_node(false, "eval_cmp_static");
  if (jmp.src == EbSrc::Imm && jmp.imm == -1)
    return bool_node(false, "eval_cmp_static");
  RNode dst = regs[jmp.dst].node;
  if (regs[jmp.dst].tag == CellTag::Pointer)
    pointer = true;
  RNode src;
  if (jmp.src == EbSrc::Reg) {
    src = regs[jmp.src_reg].node;
    if (regs[jmp.src_reg].tag == CellTag::Pointer)
      pointer = true;
  } else {
    src = const_node(imm_bits(jmp.imm), "eval_cmp64");
  }
  RNode cond = wrap(RNode::Kind::Ugt, "eval_cmp64", std::move(dst), std::move(src));
  if (jmp.src == EbSrc::Imm && jmp.imm == 10)
    cond.note = "eval_cmp_static not applied";
  return cond;
}

bool build_blocks(const std::vector<EbInsn> &code, std::vector<PBlock> &blocks) {
  const int n = static_cast<int>(code.size());
  std::vector<char> leader(n, 0);
  leader[0] = 1;
  bool loop = false;
  for (int i = 0; i < n; ++i) {
    if (!std::holds_alternative<EbJmp>(code[i].op))
      continue;
    const auto &jmp = std::get<EbJmp>(code[i].op);
    if (jmp.op != EbJmp::Exit) {
      int target = jump_target(code[i]);
      if (target < 0 || target >= n)
        throw std::runtime_error("jump target out of range");
      leader[target] = 1;
      if (target <= i)
        loop = true;
    }
    if (i + 1 < n)
      leader[i + 1] = 1;
  }
  std::vector<int> block_of(n, -1);
  for (int i = 0; i < n; ++i) {
    if (!leader[i])
      continue;
    PBlock block;
    block.start = i;
    block.end = n;
    if (!blocks.empty())
      blocks.back().end = i;
    block_of[i] = static_cast<int>(blocks.size());
    blocks.push_back(block);
  }
  for (int bi = 0; bi < static_cast<int>(blocks.size()); ++bi) {
    auto &block = blocks[bi];
    const auto &last = code[block.end - 1];
    auto edge = [&](int insn_index) {
      int dest = block_of[insn_index];
      block.succ.push_back(dest);
      blocks[dest].pred.push_back(bi);
    };
    if (const auto *jmp = std::get_if<EbJmp>(&last.op)) {
      if (jmp->op == EbJmp::Exit) {
        continue;
      }
      if (jmp->op == EbJmp::Ja) {
        edge(jump_target(last));
      } else {
        edge(jump_target(last));
        edge(block.end);
      }
    } else if (block.end < n) {
      edge(block.end);
    } else {
      throw std::runtime_error("program falls off the end without EXIT");
    }
  }
  blocks[0].pred.push_back(-1);
  return loop;
}

RReg merge_reg(const RNode &cond, const RReg &left, const RReg &right) {
  if (left.tag == right.tag && same_node(left.node, right.node))
    return left;
  if (left.tag == CellTag::Pointer || right.tag == CellTag::Pointer)
    return reg_of(pointer_node(), CellTag::Pointer);
  if (left.tag == CellTag::Undef && right.tag == CellTag::Undef)
    return left;
  RNode ite = node_of(RNode::Kind::Ite, "exec_jmpcmp");
  ite.tag = CellTag::Bits;
  ite.kids = {cond, left.node, right.node};
  return reg_of(std::move(ite), CellTag::Bits);
}

std::vector<DraftPc>
project(const std::vector<EbInsn> &code,
        const std::vector<std::pair<uint8_t, std::string>> &inputs, bool &loop) {
  std::vector<PBlock> blocks;
  loop = build_blocks(code, blocks);
  std::vector<DraftPc> pcs;
  if (loop)
    return pcs;
  std::vector<Sim> sims(blocks.size());
  auto initial = entry_regs(inputs);
  std::vector<char> done(blocks.size(), 0);
  int left = static_cast<int>(blocks.size());
  while (left) {
    bool progress = false;
    for (int bi = 0; bi < static_cast<int>(blocks.size()); ++bi) {
      if (done[bi])
        continue;
      int pending = 0;
      int ready = 0;
      for (int pred : blocks[bi].pred) {
        if (pred < 0 || done[pred])
          ++ready;
        else
          ++pending;
      }
      if (ready == 0)
        continue;
      if (pending)
        throw std::runtime_error("eBPF CFG is not reducible");
      std::vector<std::pair<RNode, std::array<RReg, 10>>> incoming;
      if (bi == 0) {
        incoming.push_back({bool_node(true, "nextinstr"), initial});
      }
      for (int pred : blocks[bi].pred) {
        if (pred < 0)
          continue;
        for (const auto &edge : sims[pred].edges) {
          if (edge.block == bi)
            incoming.push_back({edge.cond, sims[pred].out});
        }
      }
      if (incoming.empty())
        throw std::runtime_error("block has no incoming projection");
      Sim sim;
      std::array<RReg, 10> regs{};
      if (incoming.size() == 1) {
        sim.path = incoming[0].first;
        regs = incoming[0].second;
      } else if (incoming.size() == 2) {
        sim.path = lor(incoming[0].first, incoming[1].first, "exec_jmpcmp");
        for (int reg = 0; reg < 10; ++reg)
          regs[reg] = merge_reg(incoming[0].first, incoming[0].second[reg],
                                incoming[1].second[reg]);
      } else {
        throw std::runtime_error("projection does not join more than two paths");
      }
      sim.in = regs;
      for (int pc = blocks[bi].start; pc < blocks[bi].end; ++pc) {
        const auto &insn = code[pc];
        DraftPc draft;
        draft.pc = insn.index;
        draft.insn = format_insn(insn);
        while (!draft.insn.empty() &&
               (draft.insn.back() == '\n' || draft.insn.back() == '\r'))
          draft.insn.pop_back();
        auto colon = draft.insn.find(": ");
        if (colon != std::string::npos)
          draft.insn = draft.insn.substr(colon + 2);
        draft.path = sim.path;
        draft.pre = regs;
        if (!supported_insn(insn)) {
          draft.unsupported = true;
          draft.reason = "opcode is outside the projection";
          draft.post = regs;
          draft.rules = {"unsupported"};
          pcs.push_back(std::move(draft));
          continue;
        }
        if (const auto *alu = std::get_if<EbAlu>(&insn.op)) {
          bool pointer = false;
          std::string reason;
          regs[alu->dst] = eval_alu(*alu, draft.pre, pointer, reason);
          draft.pointer_use = pointer;
          draft.reason = reason;
          draft.post = regs;
          draft.rules = {"exec_alu", alu->op == EbAlu::Div ? "eval_div_u64" : "eval_alu64",
                         "nextinstr"};
          if (pc == blocks[bi].end - 1) {
            for (int dest : blocks[bi].succ) {
              PEdge edge;
              edge.block = dest;
              edge.target_pc = blocks[dest].start;
              edge.cond = sim.path;
              draft.edges.push_back(edge);
            }
          }
        } else {
          const auto &jmp = std::get<EbJmp>(insn.op);
          draft.post = regs;
          if (jmp.op == EbJmp::Exit) {
            draft.rules = {"exec_ret"};
            PEdge edge;
            edge.exit = true;
            edge.cond = sim.path;
            draft.edges.push_back(edge);
          } else if (jmp.op == EbJmp::Ja) {
            draft.rules = {"exec_jmp64", "nextinstr"};
            PEdge edge;
            edge.block = blocks[bi].succ[0];
            edge.target_pc = blocks[edge.block].start;
            edge.cond = sim.path;
            draft.edges.push_back(edge);
          } else {
            bool pointer = false;
            RNode taken = jgt_cond(jmp, regs, pointer);
            draft.pointer_use = pointer;
            if (pointer)
              draft.reason = "bitvector use of a pointer register";
            draft.rules = {"exec_jmpcmp", "eval_cmp_static", "eval_cmp64", "nextinstr"};
            PEdge go;
            go.block = blocks[bi].succ[0];
            go.target_pc = blocks[go.block].start;
            go.cond = land(sim.path, taken, "exec_jmpcmp");
            PEdge stay;
            stay.block = blocks[bi].succ[1];
            stay.target_pc = blocks[stay.block].start;
            stay.cond = land(sim.path, lnot(taken, "exec_jmpcmp"), "exec_jmpcmp");
            draft.edges = {std::move(go), std::move(stay)};
          }
        }
        pcs.push_back(std::move(draft));
      }
      sim.out = regs;
      if (!pcs.empty() && pcs.back().pc == code[blocks[bi].end - 1].index)
        sim.edges = pcs.back().edges;
      sim.ready = true;
      sims[bi] = std::move(sim);
      done[bi] = 1;
      --left;
      progress = true;
    }
    if (!progress)
      throw std::runtime_error("eBPF CFG is not reducible");
  }
  return pcs;
}

std::optional<smt::expr> lower(const RNode &node) {
  auto child = [&](size_t i) -> std::optional<smt::expr> {
    if (i >= node.kids.size())
      return std::nullopt;
    return lower(node.kids[i]);
  };
  switch (node.kind) {
  case RNode::Kind::Const:
    return smt::expr::mkUInt(node.imm, 64);
  case RNode::Kind::Var:
    return smt::expr::mkVar(node.var.c_str(), 64);
  case RNode::Kind::True:
    return smt::expr(true);
  case RNode::Kind::False:
    return smt::expr(false);
  case RNode::Kind::Add: {
    auto left = child(0);
    auto right = child(1);
    if (!left || !right)
      return std::nullopt;
    return *left + *right;
  }
  case RNode::Kind::Sub: {
    auto left = child(0);
    auto right = child(1);
    if (!left || !right)
      return std::nullopt;
    return *left - *right;
  }
  case RNode::Kind::Udiv: {
    auto left = child(0);
    auto right = child(1);
    if (!left || !right)
      return std::nullopt;
    return left->udiv(*right);
  }
  case RNode::Kind::Eq: {
    auto left = child(0);
    auto right = child(1);
    if (!left || !right)
      return std::nullopt;
    return *left == *right;
  }
  case RNode::Kind::Ugt: {
    auto left = child(0);
    auto right = child(1);
    if (!left || !right)
      return std::nullopt;
    return left->ugt(*right);
  }
  case RNode::Kind::Not: {
    auto value = child(0);
    if (!value)
      return std::nullopt;
    return !(*value);
  }
  case RNode::Kind::And: {
    auto left = child(0);
    auto right = child(1);
    if (!left || !right)
      return std::nullopt;
    return *left && *right;
  }
  case RNode::Kind::Or: {
    auto left = child(0);
    auto right = child(1);
    if (!left || !right)
      return std::nullopt;
    return *left || *right;
  }
  case RNode::Kind::Ite: {
    auto cond = child(0);
    auto then = child(1);
    auto els = child(2);
    if (!cond || !then || !els)
      return std::nullopt;
    return smt::expr::mkIf(*cond, *then, *els);
  }
  case RNode::Kind::Undef:
  case RNode::Kind::Pointer:
    return std::nullopt;
  }
  return std::nullopt;
}

bool zero_const(const smt::expr &expr) {
  return expr.isValid() && expr.isBV() && expr.isConst() && expr.isZero();
}

Verdict definedness_of(CellTag alive, CellTag rocq, const smt::expr &expr) {
  if (rocq == CellTag::Undef) {
    if (alive == CellTag::Undef && !zero_const(expr))
      return Verdict::Equivalent;
    return Verdict::Counterexample;
  }
  if (alive == CellTag::Undef && rocq == CellTag::Zero)
    return Verdict::Counterexample;
  if (alive == rocq)
    return Verdict::Equivalent;
  return Verdict::Counterexample;
}

smt::expr input_assume(const std::vector<std::pair<uint8_t, std::string>> &inputs) {
  smt::expr assume = true;
  for (auto [reg, name] : inputs) {
    (void)reg;
    auto undef = smt::expr::mkVar(("isundef_" + name).c_str(), 1);
    auto poison = smt::expr::mkBoolVar(("np_" + name).c_str());
    assume = assume && poison && undef == 0;
  }
  return assume;
}

Verdict prove(const smt::expr &alive, const std::optional<smt::expr> &rocq,
              const smt::expr &assume, std::string &model) {
  if (!alive.isValid() || !rocq || !rocq->isValid() || !alive.isSameTypeOf(*rocq))
    return Verdict::Unsupported;
  auto result = smt::check_expr(assume && !(alive == *rocq), "ebpf-project", true);
  if (result.isUnsat())
    return Verdict::Equivalent;
  if (result.isSat()) {
    std::ostringstream printed;
    printed << result.getModel();
    model = printed.str();
    return Verdict::Counterexample;
  }
  model = result.getReason().empty() ? "solver returned no model" : result.getReason();
  return Verdict::Unknown;
}

std::string show_expr(const smt::expr &expr) {
  if (!expr.isValid())
    return "";
  std::ostringstream printed;
  printed << expr;
  return printed.str();
}

void collect_leaves(const RNode &node, std::vector<const RNode *> &leaves) {
  if (node.kind == RNode::Kind::Ite && node.kids.size() == 3) {
    collect_leaves(node.kids[1], leaves);
    collect_leaves(node.kids[2], leaves);
    return;
  }
  leaves.push_back(&node);
}

CheckedCell check_cell(const AliveCell &alive, const RReg &rocq, const smt::expr &assume,
                       bool force_unsupported) {
  CheckedCell cell;
  cell.alive_tag = alive.tag;
  cell.rocq_tag = rocq.tag;
  cell.alive = alive.structure;
  cell.rocq = rocq.node;
  cell.smt = show_expr(alive.value);
  cell.definedness = definedness_of(alive.tag, rocq.tag, alive.value);
  if (force_unsupported || alive.tag == CellTag::Pointer || rocq.tag == CellTag::Pointer) {
    cell.value = Verdict::Unsupported;
    return cell;
  }
  if (alive.tag == CellTag::Undef || rocq.tag == CellTag::Undef) {
    cell.value = Verdict::Unsupported;
    return cell;
  }
  if (alive.missing || alive.structure.partial) {
    cell.value = Verdict::Unsupported;
    return cell;
  }
  auto lowered = lower(rocq.node);
  cell.value = prove(alive.value, lowered, assume, cell.model);
  return cell;
}

CheckedProgram finish(const std::string &label, const std::string &bytes, LiftBug bug,
                      const std::vector<uint8_t> &code,
                      std::vector<std::pair<uint8_t, std::string>> inputs) {
  static smt::smt_initializer smt;
  (void)smt;
  CheckedProgram program;
  program.label = label;
  program.bytes = bytes;
  program.bug = bug == LiftBug::DivZeroAsUb ? "div-zero-as-ub" : "none";
  auto alive = observe_ebpf(code, inputs, bug);
  program.loop = alive.loop;
  if (alive.loop) {
    CheckedPc pc;
    pc.reason = "back edge";
    pc.path = Verdict::Unsupported;
    program.pcs.push_back(pc);
    return program;
  }
  bool loop = false;
  auto draft = project(decode_ebpf(code), inputs, loop);
  if (loop) {
    program.loop = true;
    CheckedPc pc;
    pc.reason = "back edge";
    pc.path = Verdict::Unsupported;
    program.pcs.push_back(pc);
    return program;
  }
  auto assume = input_assume(inputs);
  for (const auto &site : alive.pcs) {
    const DraftPc *rocq = nullptr;
    for (const auto &candidate : draft) {
      if (candidate.pc == site.pc)
        rocq = &candidate;
    }
    CheckedPc pc;
    pc.pc = site.pc;
    pc.block = site.block;
    pc.path_smt = show_expr(site.path);
    pc.alive_path = site.path_structure;
    if (!rocq) {
      pc.reason = "projection has no pc";
      pc.path = Verdict::Unsupported;
      program.pcs.push_back(std::move(pc));
      continue;
    }
    pc.insn = rocq->insn;
    pc.rules = rocq->rules;
    pc.rocq_path = rocq->path;
    pc.reason = rocq->reason;
    bool blocked = rocq->unsupported || rocq->pointer_use || site.pointer_use;
    if (blocked && pc.reason.empty())
      pc.reason = rocq->unsupported ? "opcode is outside the projection"
                                    : "bitvector use of a pointer register";
    if (site.path_structure.partial || blocked)
      pc.path = Verdict::Unsupported;
    else
      pc.path = prove(site.path, lower(rocq->path), assume, pc.path_model);
    pc.pre.reserve(10);
    pc.post.reserve(10);
    for (int reg = 0; reg < 10; ++reg) {
      pc.pre.push_back(check_cell(site.pre[reg], rocq->pre[reg], assume, blocked));
      pc.post.push_back(check_cell(site.post[reg], rocq->post[reg], assume, blocked));
    }
    for (const auto &edge : site.edges) {
      CheckedEdge out;
      out.block = edge.block;
      out.target_pc = edge.target_pc;
      out.exit = edge.exit;
      out.alive = edge.structure;
      out.smt = show_expr(edge.cond);
      const PEdge *match = nullptr;
      for (const auto &candidate : rocq->edges) {
        if (candidate.exit == edge.exit && candidate.target_pc == edge.target_pc)
          match = &candidate;
      }
      if (!match || edge.structure.partial || blocked) {
        out.verdict = Verdict::Unsupported;
      } else {
        out.rocq = match->cond;
        out.verdict = prove(edge.cond, lower(match->cond), assume, out.model);
      }
      pc.edges.push_back(std::move(out));
    }
    for (const auto &phi : site.phis) {
      if (phi.reg < 0 || phi.reg > 9)
        continue;
      std::vector<const RNode *> arms;
      collect_leaves(rocq->post[phi.reg].node, arms);
      CheckedPhi checked;
      checked.reg = phi.reg;
      checked.pred = phi.pred;
      checked.alive = phi.incoming.structure;
      checked.smt = show_expr(phi.incoming.value);
      if (blocked || phi.incoming.structure.partial || phi.incoming.missing || arms.empty()) {
        checked.verdict = Verdict::Unsupported;
      } else {
        Verdict best = Verdict::Unsupported;
        std::string model;
        for (const RNode *arm : arms) {
          std::string arm_model;
          auto verdict = prove(phi.incoming.value, lower(*arm), assume, arm_model);
          if (verdict == Verdict::Equivalent) {
            best = verdict;
            checked.rocq = *arm;
            model.clear();
            break;
          }
          if (best == Verdict::Unsupported || verdict == Verdict::Counterexample) {
            best = verdict;
            model = arm_model;
            checked.rocq = *arm;
          }
        }
        checked.verdict = best;
        checked.model = model;
      }
      pc.phis.push_back(std::move(checked));
    }
    program.pcs.push_back(std::move(pc));
  }
  return program;
}

std::optional<uint64_t> eval_node(const RNode &node,
                                  const std::vector<std::pair<uint8_t, uint64_t>> &env) {
  auto child = [&](size_t i) -> std::optional<uint64_t> {
    if (i >= node.kids.size())
      return std::nullopt;
    return eval_node(node.kids[i], env);
  };
  switch (node.kind) {
  case RNode::Kind::Const:
    return node.imm;
  case RNode::Kind::Var:
    for (auto [reg, bits] : env) {
      if (node.var == "r" + std::to_string(reg))
        return bits;
    }
    return std::nullopt;
  case RNode::Kind::True:
    return 1;
  case RNode::Kind::False:
    return 0;
  case RNode::Kind::Add: {
    auto left = child(0);
    auto right = child(1);
    if (!left || !right)
      return std::nullopt;
    return *left + *right;
  }
  case RNode::Kind::Sub: {
    auto left = child(0);
    auto right = child(1);
    if (!left || !right)
      return std::nullopt;
    return *left - *right;
  }
  case RNode::Kind::Udiv: {
    auto left = child(0);
    auto right = child(1);
    if (!left || !right || *right == 0)
      return right && *right == 0 ? std::optional<uint64_t>(0) : std::nullopt;
    return *left / *right;
  }
  case RNode::Kind::Eq: {
    auto left = child(0);
    auto right = child(1);
    if (!left || !right)
      return std::nullopt;
    return *left == *right ? 1 : 0;
  }
  case RNode::Kind::Ugt: {
    auto left = child(0);
    auto right = child(1);
    if (!left || !right)
      return std::nullopt;
    return *left > *right ? 1 : 0;
  }
  case RNode::Kind::Not: {
    auto value = child(0);
    if (!value)
      return std::nullopt;
    return *value == 0 ? 1 : 0;
  }
  case RNode::Kind::And: {
    auto left = child(0);
    auto right = child(1);
    if (!left || !right)
      return std::nullopt;
    return (*left != 0 && *right != 0) ? 1 : 0;
  }
  case RNode::Kind::Or: {
    auto left = child(0);
    auto right = child(1);
    if (!left || !right)
      return std::nullopt;
    return (*left != 0 || *right != 0) ? 1 : 0;
  }
  case RNode::Kind::Ite: {
    auto cond = child(0);
    auto then = child(1);
    auto els = child(2);
    if (!cond || !then || !els)
      return std::nullopt;
    return *cond != 0 ? then : els;
  }
  case RNode::Kind::Undef:
  case RNode::Kind::Pointer:
    return std::nullopt;
  }
  return std::nullopt;
}

std::string capture_rocq(const std::string &input, int &code) {
  int in_pipe[2];
  int out_pipe[2];
  if (pipe(in_pipe) != 0 || pipe(out_pipe) != 0)
    throw std::runtime_error("pipe");
  pid_t pid = fork();
  if (pid < 0)
    throw std::runtime_error("fork");
  if (pid == 0) {
    dup2(in_pipe[0], STDIN_FILENO);
    dup2(out_pipe[1], STDOUT_FILENO);
    close(in_pipe[0]);
    close(in_pipe[1]);
    close(out_pipe[0]);
    close(out_pipe[1]);
    execl(ROCQ_STEP, ROCQ_STEP, static_cast<char *>(nullptr));
    _exit(127);
  }
  close(in_pipe[0]);
  close(out_pipe[1]);
  size_t off = 0;
  while (off < input.size()) {
    ssize_t wrote = write(in_pipe[1], input.data() + off, input.size() - off);
    if (wrote < 0) {
      if (errno == EINTR)
        continue;
      break;
    }
    off += static_cast<size_t>(wrote);
  }
  close(in_pipe[1]);
  std::string out;
  char buf[4096];
  while (true) {
    ssize_t got = read(out_pipe[0], buf, sizeof buf);
    if (got < 0) {
      if (errno == EINTR)
        continue;
      break;
    }
    if (got == 0)
      break;
    out.append(buf, static_cast<size_t>(got));
  }
  close(out_pipe[0]);
  int status = 0;
  if (waitpid(pid, &status, 0) < 0)
    throw std::runtime_error("waitpid");
  code = WIFEXITED(status) ? WEXITSTATUS(status) : 1;
  return out;
}

std::string hex16(uint64_t bits) {
  char buf[17];
  std::snprintf(buf, sizeof buf, "%016llx", static_cast<unsigned long long>(bits));
  return buf;
}

std::string hex_bytes(const std::vector<uint8_t> &code) {
  static const char *digits = "0123456789abcdef";
  std::string out;
  out.resize(code.size() * 2);
  for (size_t i = 0; i < code.size(); ++i) {
    out[i * 2] = digits[code[i] >> 4];
    out[i * 2 + 1] = digits[code[i] & 0xf];
  }
  return out;
}

CrossCheck cross_one(const CheckedProgram &program, const std::vector<uint8_t> &code,
                     const std::vector<std::pair<uint8_t, uint64_t>> &inputs,
                     const std::string &label) {
  CrossCheck row;
  row.label = label;
  const CheckedPc *exit_pc = nullptr;
  for (const auto &pc : program.pcs) {
    if (pc.insn.find("exit") != std::string::npos)
      exit_pc = &pc;
  }
  if (!exit_pc || exit_pc->post.size() < 1) {
    row.error = "projection has no exit r0";
    return row;
  }
  auto projected = eval_node(exit_pc->post[0].rocq, inputs);
  if (!projected) {
    row.error = "projection r0 did not evaluate";
    return row;
  }
  row.projection = hex16(*projected);
  std::ostringstream request;
  request << "bytes " << hex_bytes(code) << "\n";
  for (auto [reg, bits] : inputs)
    request << "in " << static_cast<int>(reg) << " " << hex16(bits) << "\n";
  try {
    int code_status = 0;
    auto output = capture_rocq(request.str(), code_status);
    if (code_status != 0)
      throw std::runtime_error("rocq-step failed");
    auto trace = parse_rocq_stream(output);
    const Step *exit_step = nullptr;
    for (const auto &step : trace.steps) {
      if (step.status == StepStatus::Exit)
        exit_step = &step;
    }
    if (!exit_step || !exit_step->return_value) {
      row.error = "rocq-step returned no r0";
      return row;
    }
    row.rocq = hex16(exit_step->return_value->bits);
    row.match = row.projection == row.rocq;
    if (!row.match)
      row.error = "projection r0 disagrees with rocq-step";
  } catch (const std::exception &ex) {
    row.error = ex.what();
  }
  return row;
}

void write_alive_node(std::ostringstream &out, const AliveNode &node) {
  out << "{\"op\":\"" << json_escape(node.op) << "\",\"width\":" << node.width
      << ",\"constant\":\"" << json_escape(node.constant) << "\",\"var\":\""
      << json_escape(node.var) << "\",\"partial\":" << (node.partial ? "true" : "false")
      << ",\"children\":[";
  for (size_t i = 0; i < node.children.size(); ++i) {
    if (i)
      out << ',';
    write_alive_node(out, node.children[i]);
  }
  out << "]}";
}

void write_rocq_node(std::ostringstream &out, const RNode &node) {
  out << "{\"op\":\"" << kind_name(node.kind) << "\",\"cite\":\"" << json_escape(node.cite)
      << "\",\"note\":\"" << json_escape(node.note) << "\",\"constant\":\""
      << (node.kind == RNode::Kind::Const ? std::to_string(node.imm) : "")
      << "\",\"var\":\"" << json_escape(node.var) << "\",\"tag\":\"" << tag_name(node.tag)
      << "\",\"children\":[";
  for (size_t i = 0; i < node.kids.size(); ++i) {
    if (i)
      out << ',';
    write_rocq_node(out, node.kids[i]);
  }
  out << "]}";
}

void write_cell(std::ostringstream &out, int reg, const CheckedCell &cell) {
  out << "{\"reg\":" << reg << ",\"alive_tag\":\"" << tag_name(cell.alive_tag)
      << "\",\"rocq_tag\":\"" << tag_name(cell.rocq_tag) << "\",\"definedness\":\""
      << verdict_name(cell.definedness) << "\",\"value\":\"" << verdict_name(cell.value)
      << "\",\"model\":\"" << json_escape(cell.model) << "\",\"smt\":\""
      << json_escape(cell.smt) << "\",\"alive\":";
  write_alive_node(out, cell.alive);
  out << ",\"rocq\":";
  write_rocq_node(out, cell.rocq);
  out << '}';
}

std::vector<uint8_t> bytes_of(const char *hex) {
  std::string text(hex);
  if (text.size() % 2 != 0)
    throw std::runtime_error("odd hex length");
  std::vector<uint8_t> out;
  auto nyb = [](char c) -> int {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
  };
  for (size_t i = 0; i < text.size(); i += 2) {
    int hi = nyb(text[i]);
    int lo = nyb(text[i + 1]);
    if (hi < 0 || lo < 0)
      throw std::runtime_error("bad hex");
    out.push_back(static_cast<uint8_t>((hi << 4) | lo));
  }
  return out;
}

const Fixture *fixture_named(const char *id) {
  for (const auto &fixture : kFixtures()) {
    if (std::string(fixture.id) == id)
      return &fixture;
  }
  return nullptr;
}

std::vector<std::pair<uint8_t, std::string>> names_of(const Fixture &fixture) {
  std::vector<std::pair<uint8_t, std::string>> names;
  for (auto [reg, bits] : fixture.inputs) {
    (void)bits;
    names.emplace_back(reg, "r" + std::to_string(reg));
  }
  return names;
}

bool cell_bits_ok(const CheckedCell &cell) {
  if (cell.alive_tag == CellTag::Pointer || cell.rocq_tag == CellTag::Pointer)
    return cell.value == Verdict::Unsupported && cell.definedness == Verdict::Equivalent;
  if (cell.alive_tag == CellTag::Undef || cell.rocq_tag == CellTag::Undef)
    return cell.definedness == Verdict::Equivalent;
  return cell.value == Verdict::Equivalent && cell.definedness == Verdict::Equivalent;
}

bool program_equivalent(const CheckedProgram &program) {
  if (program.loop || program.pcs.empty())
    return false;
  for (const auto &pc : program.pcs) {
    if (pc.path != Verdict::Equivalent)
      return false;
    for (const auto &cell : pc.pre) {
      if (!cell_bits_ok(cell))
        return false;
    }
    for (const auto &cell : pc.post) {
      if (!cell_bits_ok(cell))
        return false;
    }
    for (const auto &edge : pc.edges) {
      if (edge.verdict != Verdict::Equivalent)
        return false;
    }
    for (const auto &phi : pc.phis) {
      if (phi.verdict != Verdict::Equivalent)
        return false;
    }
  }
  return true;
}

const CheckedPc *pc_with_insn(const CheckedProgram &program, const char *token) {
  const std::string needle = std::string(" ") + token;
  for (const auto &pc : program.pcs) {
    if (pc.insn.find(needle) != std::string::npos || pc.insn == token)
      return &pc;
  }
  return nullptr;
}

} // namespace

CheckedProgram analyze_bytes(const std::vector<uint8_t> &code,
                             std::vector<std::pair<uint8_t, std::string>> inputs,
                             std::vector<std::pair<uint8_t, uint64_t>> concrete,
                             LiftBug bug, const std::string &label) {
  auto program = finish(label, hex_bytes(code), bug, code, inputs);
  if (!concrete.empty() && !program.loop)
    program.cross.push_back(cross_one(program, code, concrete, label));
  return program;
}

ExhibitDoc analyze_default() {
  ExhibitDoc doc;
  doc.projection = kProjection;
  const Fixture *jgt11 = fixture_named("jgt64-11");
  const Fixture *jgt10 = fixture_named("jgt64-10");
  const Fixture *div2 = fixture_named("div64-7-2");
  const Fixture *div0 = fixture_named("div64-7-0");
  const Fixture *mut = fixture_named("div64-7-0-div-zero-as-ub");
  if (!jgt11 || !jgt10 || !div2 || !div0 || !mut)
    throw std::runtime_error("missing fixture");
  auto jgt_code = bytes_of(jgt11->bytes_hex);
  auto div_code = bytes_of(div0->bytes_hex);
  auto jgt = finish("JGT64", jgt11->bytes_hex, LiftBug::None, jgt_code, names_of(*jgt11));
  jgt.cross.push_back(cross_one(jgt, jgt_code, {{1, 11}}, "jgt64-11"));
  jgt.cross.push_back(cross_one(jgt, jgt_code, {{1, 10}}, "jgt64-10"));
  auto div = finish("DIV64", div0->bytes_hex, LiftBug::None, div_code, names_of(*div0));
  div.cross.push_back(cross_one(div, div_code, {{1, 7}, {2, 2}}, "div64-7-2"));
  div.cross.push_back(cross_one(div, div_code, {{1, 7}, {2, 0}}, "div64-7-0"));
  auto mutation = finish("DIV64 div-zero-as-ub", mut->bytes_hex, LiftBug::DivZeroAsUb,
                         div_code, names_of(*mut));
  doc.programs = {std::move(jgt), std::move(div), std::move(mutation)};
  return doc;
}

std::string exhibit_json(const ExhibitDoc &doc) {
  std::ostringstream out;
  out << "{\"projection\":\"" << json_escape(doc.projection) << "\",\"programs\":[";
  for (size_t pi = 0; pi < doc.programs.size(); ++pi) {
    const auto &program = doc.programs[pi];
    if (pi)
      out << ',';
    out << "{\"label\":\"" << json_escape(program.label) << "\",\"bytes\":\""
        << json_escape(program.bytes) << "\",\"bug\":\"" << json_escape(program.bug)
        << "\",\"loop\":" << (program.loop ? "true" : "false") << ",\"pcs\":[";
    for (size_t i = 0; i < program.pcs.size(); ++i) {
      const auto &pc = program.pcs[i];
      if (i)
        out << ',';
      out << "{\"pc\":" << pc.pc << ",\"insn\":\"" << json_escape(pc.insn)
          << "\",\"block\":\"" << json_escape(pc.block) << "\",\"reason\":\""
          << json_escape(pc.reason) << "\",\"rules\":[";
      for (size_t r = 0; r < pc.rules.size(); ++r) {
        if (r)
          out << ',';
        out << '"' << json_escape(pc.rules[r]) << '"';
      }
      out << "],\"path\":{\"verdict\":\"" << verdict_name(pc.path) << "\",\"model\":\""
          << json_escape(pc.path_model) << "\",\"smt\":\"" << json_escape(pc.path_smt)
          << "\",\"alive\":";
      write_alive_node(out, pc.alive_path);
      out << ",\"rocq\":";
      write_rocq_node(out, pc.rocq_path);
      out << "},\"pre\":[";
      for (size_t reg = 0; reg < pc.pre.size(); ++reg) {
        if (reg)
          out << ',';
        write_cell(out, static_cast<int>(reg), pc.pre[reg]);
      }
      out << "],\"post\":[";
      for (size_t reg = 0; reg < pc.post.size(); ++reg) {
        if (reg)
          out << ',';
        write_cell(out, static_cast<int>(reg), pc.post[reg]);
      }
      out << "],\"edges\":[";
      for (size_t e = 0; e < pc.edges.size(); ++e) {
        const auto &edge = pc.edges[e];
        if (e)
          out << ',';
        out << "{\"block\":\"" << json_escape(edge.block) << "\",\"target_pc\":"
            << edge.target_pc << ",\"exit\":" << (edge.exit ? "true" : "false")
            << ",\"verdict\":\"" << verdict_name(edge.verdict) << "\",\"model\":\""
            << json_escape(edge.model) << "\",\"smt\":\"" << json_escape(edge.smt)
            << "\",\"alive\":";
        write_alive_node(out, edge.alive);
        out << ",\"rocq\":";
        write_rocq_node(out, edge.rocq);
        out << '}';
      }
      out << "],\"phis\":[";
      for (size_t p = 0; p < pc.phis.size(); ++p) {
        const auto &phi = pc.phis[p];
        if (p)
          out << ',';
        out << "{\"reg\":" << phi.reg << ",\"pred\":\"" << json_escape(phi.pred)
            << "\",\"verdict\":\"" << verdict_name(phi.verdict) << "\",\"model\":\""
            << json_escape(phi.model) << "\",\"smt\":\"" << json_escape(phi.smt)
            << "\",\"alive\":";
        write_alive_node(out, phi.alive);
        out << ",\"rocq\":";
        write_rocq_node(out, phi.rocq);
        out << '}';
      }
      out << "]}";
    }
    out << "],\"cross\":[";
    for (size_t c = 0; c < program.cross.size(); ++c) {
      const auto &row = program.cross[c];
      if (c)
        out << ',';
      out << "{\"label\":\"" << json_escape(row.label) << "\",\"projection\":\""
          << json_escape(row.projection) << "\",\"rocq\":\"" << json_escape(row.rocq)
          << "\",\"match\":" << (row.match ? "true" : "false") << ",\"error\":\""
          << json_escape(row.error) << "\"}";
    }
    out << "]}";
  }
  out << "],\"concrete\":[";
  for (size_t i = 0; i < doc.concrete.size(); ++i) {
    const auto &row = doc.concrete[i];
    if (i)
      out << ',';
    out << "{\"id\":\"" << json_escape(row.id) << "\",\"agree\":"
        << (row.agree ? "true" : "false") << ",\"divergence\":\""
        << json_escape(row.divergence) << "\",\"steps\":[";
    for (size_t s = 0; s < row.steps.size(); ++s) {
      const auto &step = row.steps[s];
      if (s)
        out << ',';
      out << "{\"pc\":" << step.pc << ",\"status\":\"" << json_escape(step.status)
          << "\",\"pc_after\":\"" << json_escape(step.pc_after) << "\",\"r0\":\""
          << json_escape(step.r0) << "\"}";
    }
    out << "]}";
  }
  out << "]}";
  return out.str();
}

int symbolic_check() {
  auto doc = analyze_default();
  const CheckedProgram *jgt = nullptr;
  const CheckedProgram *div = nullptr;
  const CheckedProgram *mutation = nullptr;
  for (const auto &program : doc.programs) {
    if (program.label == "JGT64")
      jgt = &program;
    else if (program.label == "DIV64")
      div = &program;
    else if (program.bug == "div-zero-as-ub")
      mutation = &program;
  }
  bool jgt_ok = jgt && program_equivalent(*jgt);
  const CheckedPc *jgt_pc = jgt ? pc_with_insn(*jgt, "jgt") : nullptr;
  if (!jgt_pc || jgt_pc->edges.size() != 2)
    jgt_ok = false;
  bool div_ok = div && program_equivalent(*div);
  const CheckedPc *div_pc = div ? pc_with_insn(*div, "div") : nullptr;
  if (!div_pc || div_pc->post.size() < 1 || div_pc->post[0].value != Verdict::Equivalent ||
      div_pc->phis.empty())
    div_ok = false;
  bool phi_zero = false;
  if (div_pc) {
    for (const auto &phi : div_pc->phis) {
      if (phi.verdict == Verdict::Equivalent &&
          (phi.alive.op == "const" && phi.alive.constant == "0"))
        phi_zero = true;
    }
  }
  if (!phi_zero)
    div_ok = false;
  bool mutation_ok = false;
  std::string model;
  std::string path;
  std::string absent;
  if (mutation) {
    const CheckedPc *bad = pc_with_insn(*mutation, "div");
    if (bad && !bad->post.empty() && bad->post[0].value == Verdict::Counterexample) {
      mutation_ok = true;
      model = bad->post[0].model;
      path = bad->path_smt;
      if (model.empty())
        absent = bad->post[0].model.empty() ? "solver returned no model" : bad->post[0].model;
    }
  }
  bool init_ok = false;
  if (jgt) {
    for (const auto &pc : jgt->pcs) {
      if (pc.pre.empty())
        continue;
      const auto &cell = pc.pre[0];
      if (cell.alive_tag == CellTag::Undef && cell.rocq_tag == CellTag::Undef &&
          cell.definedness == Verdict::Equivalent && cell.smt != "0" &&
          cell.alive.op != "const") {
        init_ok = true;
        break;
      }
    }
  }
  bool cross_ok = true;
  for (const auto &program : doc.programs) {
    if (program.bug != "none")
      continue;
    for (const auto &row : program.cross) {
      if (!row.match)
        cross_ok = false;
    }
  }
  std::cout << "JGT bitvector " << (jgt_ok ? "EQUIVALENT" : "FAIL") << "\n";
  if (jgt_ok)
    std::cout << "JGT undef value UNSUPPORTED\n";
  std::cout << "DIV bitvector " << (div_ok ? "EQUIVALENT" : "FAIL") << "\n";
  if (div_ok)
    std::cout << "DIV undef value UNSUPPORTED\n";
  std::cout << "mutation " << (mutation_ok ? "COUNTEREXAMPLE" : "FAIL") << "\n";
  if (mutation_ok) {
    std::cout << "mutation path " << path << "\n";
    if (!model.empty())
      std::cout << "mutation model\n" << model << "\n";
    else
      std::cout << "mutation model absent: " << absent << "\n";
  }
  std::cout << "unseeded r0 " << (init_ok ? "undef" : "FAIL") << "\n";
  if (!cross_ok) {
    for (const auto &program : doc.programs) {
      for (const auto &row : program.cross) {
        if (!row.match)
          std::cout << "projection bug " << row.label << " projection " << row.projection
                    << " rocq " << row.rocq << " " << row.error << "\n";
      }
    }
  }
  if (!jgt_ok || !div_ok || !mutation_ok || !init_ok || !cross_ok) {
    for (const auto &program : doc.programs) {
      std::cerr << program.label << "\n";
      for (const auto &pc : program.pcs) {
        std::cerr << " pc " << pc.pc << " " << pc.insn << " path " << verdict_name(pc.path)
                  << " " << pc.reason << "\n";
        if (pc.path != Verdict::Equivalent && !pc.path_model.empty())
          std::cerr << "  path model " << pc.path_model << "\n";
        for (size_t reg = 0; reg < pc.post.size(); ++reg) {
          const auto &cell = pc.post[reg];
          if (cell.value == Verdict::Equivalent && cell.definedness == Verdict::Equivalent)
            continue;
          std::cerr << "  post r" << reg << " tag " << tag_name(cell.alive_tag) << "/"
                    << tag_name(cell.rocq_tag) << " definedness "
                    << verdict_name(cell.definedness) << " value " << verdict_name(cell.value)
                    << "\n";
          if (!cell.model.empty())
            std::cerr << "  model " << cell.model << "\n";
          if (!cell.smt.empty())
            std::cerr << "  smt " << cell.smt << "\n";
        }
        for (const auto &edge : pc.edges) {
          if (edge.verdict == Verdict::Equivalent)
            continue;
          std::cerr << "  edge " << edge.block << " -> " << edge.target_pc << " "
                    << verdict_name(edge.verdict) << "\n";
          if (!edge.smt.empty())
            std::cerr << "  edge smt " << edge.smt << "\n";
          if (!edge.model.empty())
            std::cerr << "  edge model " << edge.model << "\n";
        }
        for (const auto &phi : pc.phis) {
          if (phi.verdict == Verdict::Equivalent)
            continue;
          std::cerr << "  phi r" << phi.reg << " " << phi.pred << " "
                    << verdict_name(phi.verdict) << "\n";
        }
      }
    }
    return 1;
  }
  return 0;
}
