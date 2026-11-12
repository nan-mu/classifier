#include "ebpf_ref.h"

#include <stdexcept>

namespace {

uint64_t src64(const ConcreteRegs &regs, EbSrc kind, uint8_t reg, int32_t imm,
               bool sign_extend_imm) {
  if (kind == EbSrc::Reg)
    return regs.r[reg];
  if (sign_extend_imm)
    return static_cast<uint64_t>(static_cast<int64_t>(imm));
  return static_cast<uint32_t>(imm);
}

uint64_t apply_alu(EbAlu::Op op, EbWidth width, uint64_t dst, uint64_t src) {
  bool w32 = width == EbWidth::W32;
  uint32_t d32 = static_cast<uint32_t>(dst);
  uint32_t s32 = static_cast<uint32_t>(src);
  switch (op) {
  case EbAlu::Mov:
    return w32 ? s32 : src;
  case EbAlu::Add:
    return w32 ? static_cast<uint32_t>(d32 + s32) : dst + src;
  case EbAlu::Sub:
    return w32 ? static_cast<uint32_t>(d32 - s32) : dst - src;
  case EbAlu::Mul:
    return w32 ? static_cast<uint32_t>(d32 * s32) : dst * src;
  case EbAlu::Div:
    if (w32)
      return s32 == 0 ? 0 : d32 / s32;
    return src == 0 ? 0 : dst / src;
  case EbAlu::Mod:
    if (w32)
      return s32 == 0 ? d32 : d32 % s32;
    return src == 0 ? dst : dst % src;
  case EbAlu::Or:
    return w32 ? (d32 | s32) : (dst | src);
  case EbAlu::And:
    return w32 ? (d32 & s32) : (dst & src);
  case EbAlu::Xor:
    return w32 ? (d32 ^ s32) : (dst ^ src);
  case EbAlu::Lsh:
    return w32 ? static_cast<uint32_t>(d32 << (s32 & 31)) : dst << (src & 63);
  case EbAlu::Rsh:
    return w32 ? (d32 >> (s32 & 31)) : (dst >> (src & 63));
  case EbAlu::Arsh:
    if (w32)
      return static_cast<uint32_t>(static_cast<int32_t>(d32) >> (s32 & 31));
    return static_cast<uint64_t>(static_cast<int64_t>(dst) >> (src & 63));
  case EbAlu::Neg:
    return w32 ? static_cast<uint32_t>(0u - d32) : 0ull - dst;
  }
  throw std::runtime_error("reference ALU op missing");
}

bool cond_holds(EbJmp::Op op, EbWidth width, uint64_t dst, uint64_t src) {
  bool w32 = width == EbWidth::W32;
  uint32_t d32 = static_cast<uint32_t>(dst);
  uint32_t s32 = static_cast<uint32_t>(src);
  int32_t sd32 = static_cast<int32_t>(d32);
  int32_t ss32 = static_cast<int32_t>(s32);
  int64_t sd64 = static_cast<int64_t>(dst);
  int64_t ss64 = static_cast<int64_t>(src);
  switch (op) {
  case EbJmp::Jeq: return w32 ? d32 == s32 : dst == src;
  case EbJmp::Jne: return w32 ? d32 != s32 : dst != src;
  case EbJmp::Jgt: return w32 ? d32 > s32 : dst > src;
  case EbJmp::Jge: return w32 ? d32 >= s32 : dst >= src;
  case EbJmp::Jlt: return w32 ? d32 < s32 : dst < src;
  case EbJmp::Jle: return w32 ? d32 <= s32 : dst <= src;
  case EbJmp::Jsgt: return w32 ? sd32 > ss32 : sd64 > ss64;
  case EbJmp::Jsge: return w32 ? sd32 >= ss32 : sd64 >= ss64;
  case EbJmp::Jslt: return w32 ? sd32 < ss32 : sd64 < ss64;
  case EbJmp::Jsle: return w32 ? sd32 <= ss32 : sd64 <= ss64;
  default: break;
  }
  throw std::runtime_error("reference jump op missing");
}

smt::expr sx_imm(int32_t imm) {
  return smt::expr::mkInt(static_cast<int64_t>(imm), 64);
}

smt::expr zx_imm32(int32_t imm) {
  return smt::expr::mkUInt(static_cast<uint32_t>(imm), 64);
}

smt::expr lo32(const smt::expr &v) { return v.extract(31, 0); }

smt::expr to64(const smt::expr &v32) { return v32.zext(32); }

smt::expr apply_alu_sym(EbAlu::Op op, EbWidth width, smt::expr dst, smt::expr src) {
  bool w32 = width == EbWidth::W32;
  smt::expr d = w32 ? lo32(dst) : dst;
  smt::expr s = w32 ? lo32(src) : src;
  smt::expr result = d;
  switch (op) {
  case EbAlu::Mov: result = s; break;
  case EbAlu::Add: result = d + s; break;
  case EbAlu::Sub: result = d - s; break;
  case EbAlu::Mul: result = d * s; break;
  case EbAlu::Div:
    result = smt::expr::mkIf(s == 0, smt::expr::mkUInt(0, s.bits()), d.udiv(s));
    break;
  case EbAlu::Mod:
    result = smt::expr::mkIf(s == 0, d, d.urem(s));
    break;
  case EbAlu::Or: result = d | s; break;
  case EbAlu::And: result = d & s; break;
  case EbAlu::Xor: result = d ^ s; break;
  case EbAlu::Lsh:
    result = d << (s & smt::expr::mkUInt(w32 ? 31 : 63, s.bits()));
    break;
  case EbAlu::Rsh:
    result = (d.lshr(s & smt::expr::mkUInt(w32 ? 31 : 63, s.bits())));
    break;
  case EbAlu::Arsh:
    result = d.ashr(s & smt::expr::mkUInt(w32 ? 31 : 63, s.bits()));
    break;
  case EbAlu::Neg:
    result = smt::expr::mkUInt(0, d.bits()) - d;
    break;
  }
  return w32 ? to64(result) : result;
}

smt::expr cond_sym(EbJmp::Op op, EbWidth width, smt::expr dst, smt::expr src) {
  bool w32 = width == EbWidth::W32;
  smt::expr d = w32 ? lo32(dst) : dst;
  smt::expr s = w32 ? lo32(src) : src;
  switch (op) {
  case EbJmp::Jeq: return d == s;
  case EbJmp::Jne: return d != s;
  case EbJmp::Jgt: return d.ugt(s);
  case EbJmp::Jge: return d.uge(s);
  case EbJmp::Jlt: return d.ult(s);
  case EbJmp::Jle: return d.ule(s);
  case EbJmp::Jsgt: return d.sgt(s);
  case EbJmp::Jsge: return d.sge(s);
  case EbJmp::Jslt: return d.slt(s);
  case EbJmp::Jsle: return d.sle(s);
  default: break;
  }
  throw std::runtime_error("reference symbolic jump op missing");
}

struct SymState {
  std::array<smt::expr, 11> r;
  smt::expr r0;
  smt::expr returns;
};

SymState run_sym(const std::vector<EbInsn> &code, std::array<smt::expr, 11> regs,
                 int pc, unsigned fuel, unsigned depth) {
  if (depth > 64)
    throw std::runtime_error("symbolic reference recursion cap");
  if (pc < 0 || static_cast<size_t>(pc) >= code.size())
    throw std::runtime_error("symbolic reference fell off the program");
  const auto &insn = code[static_cast<size_t>(pc)];
  if (const auto *alu = std::get_if<EbAlu>(&insn.op)) {
    bool div_unsigned_imm = (alu->op == EbAlu::Div || alu->op == EbAlu::Mod) &&
                            alu->src == EbSrc::Imm;
    bool sign_imm = alu->width == EbWidth::W64 && !div_unsigned_imm;
    if (alu->op == EbAlu::Div || alu->op == EbAlu::Mod)
      sign_imm = alu->width == EbWidth::W64;
    smt::expr src = alu->op == EbAlu::Neg
                        ? smt::expr::mkUInt(0, 64)
                        : (alu->src == EbSrc::Reg
                               ? regs[alu->src_reg]
                               : (sign_imm ? sx_imm(alu->imm) : zx_imm32(alu->imm)));
    if ((alu->op == EbAlu::Div || alu->op == EbAlu::Mod) && alu->width == EbWidth::W32 &&
        alu->src == EbSrc::Imm)
      src = zx_imm32(alu->imm);
    if ((alu->op == EbAlu::Div || alu->op == EbAlu::Mod) && alu->width == EbWidth::W64 &&
        alu->src == EbSrc::Imm)
      src = sx_imm(alu->imm);
    regs[alu->dst] = apply_alu_sym(alu->op, alu->width, regs[alu->dst], src);
    return run_sym(code, regs, pc + 1, fuel, depth + 1);
  }
  const auto &jmp = std::get<EbJmp>(insn.op);
  if (jmp.op == EbJmp::Exit)
    return {regs, regs[0], true};
  int target = jump_target(insn);
  auto take = [&](unsigned next_fuel) {
    return run_sym(code, regs, target, next_fuel, depth + 1);
  };
  if (jmp.op == EbJmp::Ja) {
    unsigned next = fuel;
    if (target <= pc) {
      if (fuel == 0)
        return {regs, regs[0], false};
      next = fuel - 1;
    }
    return take(next);
  }
  bool imm_signed = true;
  smt::expr src = jmp.src == EbSrc::Reg ? regs[jmp.src_reg] : sx_imm(jmp.imm);
  if (jmp.width == EbWidth::W32 && jmp.src == EbSrc::Imm)
    src = zx_imm32(jmp.imm);
  (void)imm_signed;
  smt::expr c = cond_sym(jmp.op, jmp.width, regs[jmp.dst], src);
  unsigned t_fuel = fuel;
  if (target <= pc) {
    if (fuel == 0) {
      auto fall = run_sym(code, regs, pc + 1, fuel, depth + 1);
      return {regs, smt::expr::mkIf(c, regs[0], fall.r0),
              smt::expr::mkIf(c, smt::expr(false), fall.returns)};
    }
    t_fuel = fuel - 1;
  }
  auto taken = take(t_fuel);
  auto fall = run_sym(code, regs, pc + 1, fuel, depth + 1);
  return {regs, smt::expr::mkIf(c, taken.r0, fall.r0),
          smt::expr::mkIf(c, taken.returns, fall.returns)};
}

} // namespace

uint64_t interpret_ebpf(const std::vector<EbInsn> &code, ConcreteRegs regs,
                        uint32_t step_cap) {
  int pc = 0;
  for (uint32_t steps = 0; steps < step_cap; ++steps) {
    if (pc < 0 || static_cast<size_t>(pc) >= code.size())
      throw std::runtime_error("concrete reference fell off the program");
    const auto &insn = code[static_cast<size_t>(pc)];
    if (const auto *alu = std::get_if<EbAlu>(&insn.op)) {
      bool sign_imm = alu->width == EbWidth::W64;
      if (alu->op == EbAlu::Div || alu->op == EbAlu::Mod)
        sign_imm = alu->width == EbWidth::W64;
      uint64_t src = 0;
      if (alu->op != EbAlu::Neg)
        src = src64(regs, alu->src, alu->src_reg, alu->imm, sign_imm);
      regs.r[alu->dst] = apply_alu(alu->op, alu->width, regs.r[alu->dst], src);
      ++pc;
      continue;
    }
    const auto &jmp = std::get<EbJmp>(insn.op);
    if (jmp.op == EbJmp::Exit)
      return regs.r[0];
    int target = jump_target(insn);
    if (jmp.op == EbJmp::Ja) {
      pc = target;
      continue;
    }
    bool sign_imm = jmp.width == EbWidth::W64;
    uint64_t src = src64(regs, jmp.src, jmp.src_reg, jmp.imm, sign_imm);
    if (cond_holds(jmp.op, jmp.width, regs.r[jmp.dst], src))
      pc = target;
    else
      ++pc;
  }
  throw std::runtime_error("concrete reference step cap");
}

SymRef interpret_ebpf_sym(const std::vector<EbInsn> &code,
                          const std::array<smt::expr, 11> &regs,
                          unsigned backedge_fuel) {
  auto done = run_sym(code, regs, 0, backedge_fuel, 0);
  return {done.r0, done.returns};
}
