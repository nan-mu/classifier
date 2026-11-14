#include "ebpf_gate.h"

#include <deque>
#include <optional>

namespace {

constexpr uint16_t kGpr = 0x3ff;

uint16_t bit_of(unsigned reg) {
  return static_cast<uint16_t>(1u << reg);
}

enum class OpKind {
  MovImm, MovReg, Neg, AluImm, AluReg, Ja, Exit, CmpImm, CmpReg
};

OpKind op_kind(const EbInsn &insn) {
  if (const auto *alu = std::get_if<EbAlu>(&insn.op)) {
    if (alu->op == EbAlu::Neg)
      return OpKind::Neg;
    if (alu->op == EbAlu::Mov && alu->src == EbSrc::Imm)
      return OpKind::MovImm;
    if (alu->op == EbAlu::Mov || alu->op == EbAlu::Movsx)
      return OpKind::MovReg;
    if (alu->src == EbSrc::Reg)
      return OpKind::AluReg;
    return OpKind::AluImm;
  }
  const auto &jmp = std::get<EbJmp>(insn.op);
  if (jmp.op == EbJmp::Ja)
    return OpKind::Ja;
  if (jmp.op == EbJmp::Exit)
    return OpKind::Exit;
  if (jmp.src == EbSrc::Reg)
    return OpKind::CmpReg;
  return OpKind::CmpImm;
}

struct RawSucc {
  SuccKind kind;
  int pc = 0;
};

struct Effects {
  uint16_t reads = 0;
  uint16_t writes = 0;
  std::vector<RawSucc> succs;
};

Effects effects(const EbInsn &insn) {
  uint8_t dst = 0;
  uint8_t src = 0;
  if (const auto *alu = std::get_if<EbAlu>(&insn.op)) {
    dst = alu->dst;
    src = alu->src_reg;
  } else {
    const auto &jmp = std::get<EbJmp>(insn.op);
    dst = jmp.dst;
    src = jmp.src_reg;
  }
  int next = static_cast<int>(insn.index) + 1;
  Effects out;
  switch (op_kind(insn)) {
  case OpKind::MovImm:
    out.writes = bit_of(dst);
    out.succs.push_back({SuccKind::Fall, next});
    break;
  case OpKind::MovReg:
    out.reads = bit_of(src);
    out.writes = bit_of(dst);
    out.succs.push_back({SuccKind::Fall, next});
    break;
  case OpKind::Neg:
    out.reads = bit_of(dst);
    out.writes = bit_of(dst);
    out.succs.push_back({SuccKind::Fall, next});
    break;
  case OpKind::AluImm:
    out.reads = bit_of(dst);
    out.writes = bit_of(dst);
    out.succs.push_back({SuccKind::Fall, next});
    break;
  case OpKind::AluReg:
    out.reads = static_cast<uint16_t>(bit_of(dst) | bit_of(src));
    out.writes = bit_of(dst);
    out.succs.push_back({SuccKind::Fall, next});
    break;
  case OpKind::Ja:
    out.succs.push_back({SuccKind::Jump, jump_target(insn)});
    break;
  case OpKind::Exit:
    out.reads = bit_of(0);
    out.succs.push_back({SuccKind::Exit, 0});
    break;
  case OpKind::CmpImm:
    out.reads = bit_of(dst);
    out.succs.push_back({SuccKind::Jump, jump_target(insn)});
    out.succs.push_back({SuccKind::Fall, next});
    break;
  case OpKind::CmpReg:
    out.reads = static_cast<uint16_t>(bit_of(dst) | bit_of(src));
    out.succs.push_back({SuccKind::Jump, jump_target(insn)});
    out.succs.push_back({SuccKind::Fall, next});
    break;
  }
  return out;
}

bool in_program(int target, size_t n) {
  return target >= 0 && static_cast<size_t>(target) < n;
}

struct Issue {
  uint32_t pc = 0;
  int rank = 0;
  GateKind kind = GateKind::Reject;
  std::string reason;
};

struct Joined {
  uint16_t defined = 0;
  bool changed = false;
};

Joined join_defined(bool seen, uint16_t current, uint16_t outgoing) {
  if (!seen)
    return Joined{outgoing, true};
  uint16_t next = static_cast<uint16_t>(current & outgoing);
  return Joined{next, next != current};
}

}

Gate gate(const std::vector<EbInsn> &insns, const std::vector<RegNum> &seeds) {
  Gate result;
  const size_t n = insns.size();
  if (n == 0) {
    result.kind = GateKind::IllFormed;
    result.pc = 0;
    result.reason = "empty program";
    return result;
  }

  uint16_t entry = 0;
  for (RegNum reg : seeds)
    entry = static_cast<uint16_t>(entry | bit_of(reg.index()));

  std::vector<Effects> fx;
  fx.reserve(n);
  result.nodes.reserve(n);
  std::optional<Issue> best;
  auto consider = [&](Issue issue) {
    if (!best || issue.pc < best->pc ||
        (issue.pc == best->pc && issue.rank < best->rank))
      best = std::move(issue);
  };

  for (size_t i = 0; i < n; ++i) {
    Effects effect = effects(insns[i]);
    GateNode node;
    node.pc = insns[i].index;
    bool saw_r10_read = (effect.reads & bit_of(10)) != 0;
    bool saw_r10_write = (effect.writes & bit_of(10)) != 0;
    if (saw_r10_read || saw_r10_write) {
      Issue issue;
      issue.pc = node.pc;
      issue.rank = 0;
      issue.kind = GateKind::Reject;
      if (saw_r10_read && saw_r10_write)
        issue.reason = "r10 read and write";
      else if (saw_r10_read)
        issue.reason = "r10 read";
      else
        issue.reason = "r10 write";
      consider(std::move(issue));
    }
    for (const auto &succ : effect.succs) {
      if (succ.kind == SuccKind::Exit) {
        node.succs.push_back(Succ{SuccKind::Exit, 0});
        continue;
      }
      if (!in_program(succ.pc, n)) {
        Issue issue;
        issue.pc = node.pc;
        issue.rank = 2;
        issue.kind = GateKind::IllFormed;
        issue.reason = succ.kind == SuccKind::Jump ? "target outside the program"
                                                   : "fall off the end";
        consider(std::move(issue));
        continue;
      }
      node.succs.push_back(
          Succ{succ.kind, static_cast<uint32_t>(succ.pc)});
    }
    fx.push_back(std::move(effect));
    result.nodes.push_back(std::move(node));
  }

  std::vector<uint16_t> incoming(n, 0);
  std::vector<char> reached(n, 0);
  std::vector<char> queued(n, 0);
  incoming[0] = entry;
  reached[0] = 1;
  std::deque<uint32_t> work;
  work.push_back(0);
  queued[0] = 1;
  while (!work.empty()) {
    uint32_t pc = work.front();
    work.pop_front();
    queued[pc] = 0;
    uint16_t outgoing =
        static_cast<uint16_t>((incoming[pc] | fx[pc].writes) & kGpr);
    for (const auto &succ : fx[pc].succs) {
      if (succ.kind == SuccKind::Exit || !in_program(succ.pc, n))
        continue;
      auto dest = static_cast<uint32_t>(succ.pc);
      Joined joined = join_defined(reached[dest], incoming[dest], outgoing);
      if (!joined.changed)
        continue;
      reached[dest] = 1;
      incoming[dest] = joined.defined;
      if (!queued[dest]) {
        work.push_back(dest);
        queued[dest] = 1;
      }
    }
  }

  for (uint32_t pc = 0; pc < n; ++pc) {
    if (!reached[pc])
      continue;
    uint16_t missing =
        static_cast<uint16_t>((fx[pc].reads & kGpr) & ~incoming[pc]);
    for (unsigned reg = 0; reg < 10; ++reg) {
      if ((missing & bit_of(reg)) == 0)
        continue;
      Issue issue;
      issue.pc = pc;
      issue.rank = 1;
      issue.kind = GateKind::Reject;
      issue.reason = "r" + std::to_string(reg) + " read before define";
      consider(std::move(issue));
      break;
    }
  }

  if (best) {
    result.kind = best->kind;
    result.pc = best->pc;
    result.reason = best->reason;
  }
  return result;
}
