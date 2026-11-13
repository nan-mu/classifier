#include "ebpf_lift.h"
#include "ebpf_concrete.h"

#include "ir/constant.h"
#include "ir/instr.h"

#include <array>
#include <optional>
#include <sstream>
#include <unordered_map>

namespace {

using namespace IR;

enum class CommitKind { AtEntry, AfterInstr };

struct SourceEnd {
  uint32_t index = 0;
  CommitKind kind = CommitKind::AtEntry;
  BasicBlock *block = nullptr;
  Instr *after = nullptr;
  std::array<Value *, 11> regs{};
  bool flushed = false;
};

enum class IrOp { Add, Sub, And, UDiv, SDiv, ICmpEq, ICmpUgt };
enum class IrResultKind { Bits, I1, Ub, Unsupported };

struct IrResult {
  IrResultKind kind = IrResultKind::Unsupported;
  uint64_t bits = 0;
};

// Alive2's div_ub, checked before the C++ operator. Signed division of the
// signed minimum by -1 is undefined in C++ as well. A zero divisor has no
// numeric result here.
IrResult eval_op(IrOp op, uint64_t a, uint64_t b, unsigned width) {
  if (width == 0 || width > 64)
    return {};
  uint64_t mask = width == 64 ? ~uint64_t{0} : (uint64_t{1} << width) - 1;
  a &= mask;
  b &= mask;
  auto bits = [&](uint64_t v) {
    return IrResult{IrResultKind::Bits, width == 64 ? v : (v & mask)};
  };
  auto flag = [&](bool v) {
    return IrResult{IrResultKind::I1, v ? 1ull : 0ull};
  };
  if (op == IrOp::UDiv || op == IrOp::SDiv) {
    bool sign = op == IrOp::SDiv;
    uint64_t smin = uint64_t{1} << (width - 1);
    if (b == 0 || (sign && a == smin && b == mask))
      return {IrResultKind::Ub, 0};
    if (!sign)
      return bits(a / b);
    int64_t sa;
    int64_t sb;
    if (width == 64) {
      sa = static_cast<int64_t>(a);
      sb = static_cast<int64_t>(b);
    } else {
      uint64_t signbit = uint64_t{1} << (width - 1);
      sa = (a & signbit) ? static_cast<int64_t>(a | ~mask)
                         : static_cast<int64_t>(a);
      sb = (b & signbit) ? static_cast<int64_t>(b | ~mask)
                         : static_cast<int64_t>(b);
    }
    return bits(static_cast<uint64_t>(sa / sb));
  }
  switch (op) {
  case IrOp::Add: return bits(a + b);
  case IrOp::Sub: return bits(a - b);
  case IrOp::And: return bits(a & b);
  case IrOp::ICmpEq: return flag(a == b);
  case IrOp::ICmpUgt: return flag(a > b);
  default: break;
  }
  return {};
}

struct Block {
  int start = 0;
  int end = 0;
  BasicBlock *entry = nullptr;
  BasicBlock *exit = nullptr;
  std::array<Value *, 11> in{};
  std::array<Value *, 11> out{};
  std::array<Phi *, 11> phi{};
  std::vector<int> succ;
  std::vector<int> pred;
  bool done = false;
};

class Lifter {
 public:
  Lifter(Function &fn, EbTypes &types, const std::vector<EbInsn> &code,
         LiftBug bug)
      : fn(fn), i64(types.i64), i32(types.i32), i1(types.i1), i8(types.i8),
        i16(types.i16), code(code), bug(bug) {}

  LiftInfo run(const std::vector<std::pair<uint8_t, std::string>> &inputs) {
    if (code.empty())
      throw std::runtime_error("empty eBPF program");
    build_blocks();
    init_regs(inputs);
    auto &pre = fn.getBB("%entry");
    for (auto &b : blocks)
      b.entry = &fn.getBB("%b" + std::to_string(&b - blocks.data()));
    pre.addInstr(std::make_unique<Branch>(*blocks[0].entry));
    schedule();
    fill_phis(pre);
    LiftInfo info;
    info.loop = loop;
    info.cfg = cfg.str();
    return info;
  }

 private:
  Function &fn;
  IntType &i64, &i32, &i1, &i8, &i16;
  const std::vector<EbInsn> &code;
  LiftBug bug;
  std::vector<Block> blocks;
  std::vector<int> block_of;
  std::array<Value *, 11> init{};
  std::array<char, 11> written{};
  BasicBlock *cur = nullptr;
  unsigned seq = 0;
  bool loop = false;
  std::ostringstream cfg;
  std::vector<SourceEnd> ends;

  bool bare_mov(const EbAlu &alu) const {
    EbWidth width = alu.width;
    if (bug == LiftBug::Alu32AsAlu64)
      width = EbWidth::W64;
    auto op = alu.op;
    if (bug == LiftBug::AddAsSub && op == EbAlu::Add)
      op = EbAlu::Sub;
    return op == EbAlu::Mov && width == EbWidth::W64;
  }

  void note_at_entry(uint32_t index, BasicBlock *block,
                     const std::array<Value *, 11> &regs) {
    SourceEnd end;
    end.index = index;
    end.kind = CommitKind::AtEntry;
    end.block = block;
    end.regs = regs;
    ends.push_back(end);
  }

  void note_after(uint32_t index, BasicBlock *block, Instr *after,
                  const std::array<Value *, 11> &regs) {
    if (!after)
      throw std::runtime_error("commit has no instruction");
    SourceEnd end;
    end.index = index;
    end.kind = CommitKind::AfterInstr;
    end.block = block;
    end.after = after;
    end.regs = regs;
    ends.push_back(end);
  }

 public:
  Trace concrete(const std::unordered_map<std::string, uint64_t> &bound);

 private:
  std::string nm() { return "%" + std::to_string(seq++); }

  Value &add(std::unique_ptr<Instr> insn) {
    cur->addInstr(std::move(insn));
    return cur->back();
  }

  Value &c64(int64_t v) {
    auto c = std::make_unique<IntConst>(i64, v);
    Value &ref = *c;
    fn.addConstant(std::move(c));
    return ref;
  }

  Value &c32(int64_t v) {
    auto c = std::make_unique<IntConst>(i32, v);
    Value &ref = *c;
    fn.addConstant(std::move(c));
    return ref;
  }

  Value &imm64(int32_t imm, bool sign) {
    if (sign)
      return c64(static_cast<int64_t>(imm));
    return c64(static_cast<int64_t>(static_cast<uint32_t>(imm)));
  }

  Value &trunc32(Value &v) {
    return add(std::make_unique<ConversionOp>(i32, nm(), v, ConversionOp::Trunc));
  }

  Value &zext64(Value &v) {
    return add(std::make_unique<ConversionOp>(i64, nm(), v, ConversionOp::ZExt));
  }

  Value &binop(Type &ty, BinOp::Op op, Value &a, Value &b) {
    return add(std::make_unique<BinOp>(ty, nm(), a, b, op));
  }

  void build_blocks() {
    const int n = static_cast<int>(code.size());
    std::vector<char> leader(n, 0);
    leader[0] = 1;
    for (int i = 0; i < n; ++i) {
      if (!std::holds_alternative<EbJmp>(code[i].op))
        continue;
      const auto &j = std::get<EbJmp>(code[i].op);
      if (j.op != EbJmp::Exit) {
        int tgt = jump_target(code[i]);
        if (tgt < 0 || tgt >= n)
          throw std::runtime_error("jump target out of range at " +
                                   std::to_string(i));
        leader[tgt] = 1;
        if (tgt <= i)
          loop = true;
      }
      if (i + 1 < n)
        leader[i + 1] = 1;
    }
    block_of.assign(n, -1);
    for (int i = 0; i < n; ++i) {
      if (!leader[i])
        continue;
      Block b;
      b.start = i;
      b.end = n;
      if (!blocks.empty())
        blocks.back().end = i;
      block_of[i] = static_cast<int>(blocks.size());
      blocks.push_back(b);
    }
    for (int bi = 0; bi < static_cast<int>(blocks.size()); ++bi) {
      auto &b = blocks[bi];
      const auto &last = code[b.end - 1];
      auto edge = [&](int insn_index, bool taken) {
        int dest = block_of[insn_index];
        if (dest < 0)
          throw std::runtime_error("jump lands inside a block");
        if (taken && bug == LiftBug::JumpPlusOne)
          dest = (dest + 1) % static_cast<int>(blocks.size());
        b.succ.push_back(dest);
        blocks[dest].pred.push_back(bi);
      };
      if (const auto *j = std::get_if<EbJmp>(&last.op)) {
        if (j->op == EbJmp::Exit) {
          cfg << "b" << bi << " exit\n";
        } else if (j->op == EbJmp::Ja) {
          edge(jump_target(last), true);
          cfg << "b" << bi << " -> b" << b.succ.back() << "\n";
        } else {
          edge(jump_target(last), true);
          edge(b.end, false);
          cfg << "b" << bi << " -> b" << b.succ[0] << " or b" << b.succ[1] << "\n";
        }
      } else if (b.end < n) {
        edge(b.end, false);
        cfg << "b" << bi << " -> b" << b.succ.back() << "\n";
      } else {
        throw std::runtime_error("program falls off the end without EXIT");
      }
    }
    blocks[0].pred.push_back(-1);
    written[0] = 1;
    for (const auto &insn : code) {
      if (const auto *alu = std::get_if<EbAlu>(&insn.op))
        written[alu->dst] = 1;
    }
  }

  void init_regs(const std::vector<std::pair<uint8_t, std::string>> &inputs) {
    Value &zero = c64(0);
    for (auto &slot : init)
      slot = &zero;
    for (auto [reg, name] : inputs) {
      if (reg > 10)
        throw std::runtime_error("input register out of range");
      auto in = std::make_unique<Input>(i64, std::string(name));
      init[reg] = in.get();
      fn.addInput(std::move(in));
    }
  }

  void schedule() {
    int left = static_cast<int>(blocks.size());
    while (left) {
      bool progress = false;
      for (int i = 0; i < static_cast<int>(blocks.size()); ++i) {
        if (blocks[i].done)
          continue;
        int ready = 0;
        int pending = 0;
        for (int p : blocks[i].pred) {
          if (p < 0 || blocks[p].done)
            ++ready;
          else
            ++pending;
        }
        if (ready == 0)
          continue;
        if (pending || blocks[i].pred.size() > 1)
          place_phis(blocks[i], i);
        else if (blocks[i].pred[0] < 0)
          blocks[i].in = init;
        else
          blocks[i].in = blocks[blocks[i].pred[0]].out;
        emit(blocks[i], i);
        blocks[i].done = true;
        --left;
        progress = true;
      }
      if (!progress) {
        bool pending_ready = false;
        for (auto &b : blocks) {
          if (b.done)
            continue;
          for (int p : b.pred) {
            if (p < 0 || blocks[p].done)
              pending_ready = true;
          }
        }
        if (pending_ready)
          throw std::runtime_error("eBPF CFG is not reducible");
        break;
      }
    }
  }

  void place_phis(Block &b, int index) {
    bool back_edge = false;
    for (int p : b.pred) {
      if (p >= index)
        back_edge = true;
    }
    for (int r = 0; r < 11; ++r) {
      if (!written[r] && !back_edge) {
        b.in[r] = init[r];
        continue;
      }
      auto phi = std::make_unique<Phi>(i64, "%b" + std::to_string(index) + "_r" +
                                                std::to_string(r));
      b.phi[r] = phi.get();
      b.in[r] = phi.get();
      b.entry->addInstr(std::move(phi));
    }
  }

  void emit(Block &b, int) {
    cur = b.entry;
    std::array<Value *, 11> regs = b.in;
    bool emitted = false;
    Instr *anchor = nullptr;
    BasicBlock *home = b.entry;
    for (int pc = b.start; pc < b.end; ++pc) {
      const auto &insn = code[pc];
      if (const auto *alu = std::get_if<EbAlu>(&insn.op)) {
        bool bare = bare_mov(*alu);
        Value *produced = emit_alu(*alu, regs);
        regs[alu->dst] = produced;
        if (bare && !emitted) {
          note_at_entry(insn.index, b.entry, regs);
        } else if (bare) {
          note_after(insn.index, home, anchor, regs);
        } else {
          home = cur;
          anchor = dynamic_cast<Instr *>(produced);
          emitted = true;
          note_after(insn.index, home, anchor, regs);
        }
      } else if (pc != b.end - 1) {
        throw std::runtime_error("jump in the middle of a block");
      }
    }
    const auto &last = code[b.end - 1];
    if (const auto *j = std::get_if<EbJmp>(&last.op)) {
      if (j->op == EbJmp::Exit) {
        cur->addInstr(std::make_unique<Return>(i64, *regs[0]));
      } else if (j->op == EbJmp::Ja) {
        cur->addInstr(std::make_unique<Branch>(*blocks[b.succ[0]].entry));
      } else {
        Value &cond = emit_cmp(*j, regs);
        cur->addInstr(std::make_unique<Branch>(
            cond, *blocks[b.succ[0]].entry, *blocks[b.succ[1]].entry));
      }
      note_after(last.index, cur, &cur->back(), regs);
    } else {
      cur->addInstr(std::make_unique<Branch>(*blocks[b.succ[0]].entry));
    }
    b.exit = cur;
    b.out = regs;
  }

  Value *emit_alu(const EbAlu &alu, const std::array<Value *, 11> &regs) {
    EbWidth width = alu.width;
    if (bug == LiftBug::Alu32AsAlu64)
      width = EbWidth::W64;
    EbAlu::Op op = alu.op;
    if (bug == LiftBug::AddAsSub && op == EbAlu::Add)
      op = EbAlu::Sub;
    bool w32 = width == EbWidth::W32;
    bool sign_imm = width == EbWidth::W64 && bug != LiftBug::ImmNoSignExtend;
    Value *src = nullptr;
    if (op != EbAlu::Neg) {
      if (alu.src == EbSrc::Reg)
        src = regs[alu.src_reg];
      else
        src = &imm64(alu.imm, sign_imm);
    }
    if (op == EbAlu::Movsx)
      return emit_movsx(*regs[alu.src_reg], alu.offset, w32);
    if (!w32)
      return emit_wide(op, *regs[alu.dst], src);
    Value &d = trunc32(*regs[alu.dst]);
    Value *s = src ? &trunc32(*src) : nullptr;
    Value &narrow = emit_narrow(op, d, s);
    return &zext64(narrow);
  }

  Value *emit_movsx(Value &src, uint8_t bits, bool w32) {
    IntType &narrow = bits == 8 ? i8 : bits == 16 ? i16 : i32;
    Value &cut = add(std::make_unique<ConversionOp>(narrow, nm(), src,
                                                    ConversionOp::Trunc));
    Type &wide = w32 ? static_cast<Type &>(i32) : static_cast<Type &>(i64);
    auto op = bug == LiftBug::MovsxAsZext ? ConversionOp::ZExt
                                          : ConversionOp::SExt;
    Value &ext = add(std::make_unique<ConversionOp>(wide, nm(), cut, op));
    return w32 ? &zext64(ext) : &ext;
  }

  Value &shift(Value &dst, Value &src, EbAlu::Op op, bool narrow) {
    Type &ty = narrow ? static_cast<Type &>(i32) : static_cast<Type &>(i64);
    Value *amount = &src;
    if (bug != LiftBug::ShiftWithoutMask)
      amount = &binop(ty, BinOp::And, src, narrow ? c32(31) : c64(63));
    return binop(ty, shift_op(op), dst, *amount);
  }

  Value *emit_wide(EbAlu::Op op, Value &dst, Value *src) {
    if (op == EbAlu::Neg)
      return &binop(i64, BinOp::Sub, c64(0), dst);
    if (op == EbAlu::Mov)
      return src;
    if (is_divmod(op))
      return emit_divmod(i64, dst, *src, op, &dst);
    if (op == EbAlu::Lsh || op == EbAlu::Rsh || op == EbAlu::Arsh)
      return &shift(dst, *src, op, false);
    return &binop(i64, arith_op(op), dst, *src);
  }

  Value &emit_narrow(EbAlu::Op op, Value &dst, Value *src) {
    if (op == EbAlu::Neg)
      return binop(i32, BinOp::Sub, c32(0), dst);
    if (op == EbAlu::Mov)
      return *src;
    if (is_divmod(op))
      return *emit_divmod(i32, dst, *src, op, &dst);
    if (op == EbAlu::Lsh || op == EbAlu::Rsh || op == EbAlu::Arsh)
      return shift(dst, *src, op, true);
    return binop(i32, arith_op(op), dst, *src);
  }

  static bool is_divmod(EbAlu::Op op) {
    return op == EbAlu::Div || op == EbAlu::Mod || op == EbAlu::Sdiv ||
           op == EbAlu::Smod;
  }

  // eBPF defines both the zero divisor and the signed INT_MIN / -1 overflow, so
  // neither may reach Alive2's sdiv/srem, which records both as UB
  // (third_party/alive2/ir/instr.cpp:213).
  Value *emit_divmod(Type &ty, Value &dst, Value &src, EbAlu::Op op,
                     Value *keep) {
    bool is_div = op == EbAlu::Div || op == EbAlu::Sdiv;
    bool sign = op == EbAlu::Sdiv || op == EbAlu::Smod;
    BinOp::Op raw = is_div ? (sign ? BinOp::SDiv : BinOp::UDiv)
                           : (sign ? BinOp::SRem : BinOp::URem);
    if (bug == LiftBug::DivZeroAsUb ||
        (sign && bug == LiftBug::SdivOverflowAsUb))
      return &binop(ty, raw, dst, src);
    bool narrow = &ty == &i32;
    Value &zero = narrow ? c32(0) : c64(0);
    Value &minus_one = narrow ? c32(-1) : c64(-1);
    Value &smin = narrow ? c32(-2147483648ll) : c64(-9223372036854775807ll - 1);
    Value &is_zero = add(std::make_unique<ICmp>(i1, nm(), ICmp::EQ, src, zero));
    auto &zbb = fn.getBB(nm());
    auto &nbb = fn.getBB(nm());
    auto &cbb = fn.getBB(nm());
    cur->addInstr(std::make_unique<Branch>(is_zero, zbb, nbb));
    cur = &zbb;
    Value &zero_result = is_div ? zero : *keep;
    zbb.addInstr(std::make_unique<Branch>(cbb));
    cur = &nbb;
    Value *quotient = nullptr;
    BasicBlock *qbb = &nbb;
    BasicBlock *obb = nullptr;
    Value *ovf_result = nullptr;
    if (sign) {
      Value &at_smin = add(std::make_unique<ICmp>(i1, nm(), ICmp::EQ, dst, smin));
      Value &at_minus_one =
          add(std::make_unique<ICmp>(i1, nm(), ICmp::EQ, src, minus_one));
      Value &overflows = binop(i1, BinOp::And, at_smin, at_minus_one);
      obb = &fn.getBB(nm());
      qbb = &fn.getBB(nm());
      cur->addInstr(std::make_unique<Branch>(overflows, *obb, *qbb));
      cur = obb;
      ovf_result = is_div ? &dst : &zero;
      obb->addInstr(std::make_unique<Branch>(cbb));
      cur = qbb;
    }
    quotient = &binop(ty, raw, dst, src);
    qbb->addInstr(std::make_unique<Branch>(cbb));
    cur = &cbb;
    auto phi = std::make_unique<Phi>(ty, nm());
    phi->addValue(zero_result, std::string(zbb.getName()));
    if (sign)
      phi->addValue(*ovf_result, std::string(obb->getName()));
    phi->addValue(*quotient, std::string(qbb->getName()));
    return &add(std::move(phi));
  }

  Value &emit_cmp(const EbJmp &j, const std::array<Value *, 11> &regs) {
    bool w32 = j.width == EbWidth::W32;
    Value &dst = w32 ? trunc32(*regs[j.dst]) : *regs[j.dst];
    Value &src = [&]() -> Value & {
      if (j.src == EbSrc::Reg)
        return w32 ? trunc32(*regs[j.src_reg]) : *regs[j.src_reg];
      if (w32)
        return c32(static_cast<uint32_t>(j.imm));
      return c64(static_cast<int64_t>(j.imm));
    }();
    return add(std::make_unique<ICmp>(i1, nm(), icmp_cond(j.op), dst, src));
  }

  static BinOp::Op arith_op(EbAlu::Op op) {
    switch (op) {
    case EbAlu::Add: return BinOp::Add;
    case EbAlu::Sub: return BinOp::Sub;
    case EbAlu::Mul: return BinOp::Mul;
    case EbAlu::Or: return BinOp::Or;
    case EbAlu::And: return BinOp::And;
    case EbAlu::Xor: return BinOp::Xor;
    default: break;
    }
    throw std::runtime_error("not an arithmetic opcode");
  }

  static BinOp::Op shift_op(EbAlu::Op op) {
    switch (op) {
    case EbAlu::Lsh: return BinOp::Shl;
    case EbAlu::Rsh: return BinOp::LShr;
    case EbAlu::Arsh: return BinOp::AShr;
    default: break;
    }
    throw std::runtime_error("not a shift opcode");
  }

  static ICmp::Cond icmp_cond(EbJmp::Op op) {
    switch (op) {
    case EbJmp::Jeq: return ICmp::EQ;
    case EbJmp::Jne: return ICmp::NE;
    case EbJmp::Jgt: return ICmp::UGT;
    case EbJmp::Jge: return ICmp::UGE;
    case EbJmp::Jlt: return ICmp::ULT;
    case EbJmp::Jle: return ICmp::ULE;
    case EbJmp::Jsgt: return ICmp::SGT;
    case EbJmp::Jsge: return ICmp::SGE;
    case EbJmp::Jslt: return ICmp::SLT;
    case EbJmp::Jsle: return ICmp::SLE;
    default: break;
    }
    throw std::runtime_error("not a compare");
  }

  void fill_phis(BasicBlock &pre) {
    for (auto &b : blocks) {
      for (int r = 0; r < 11; ++r) {
        if (!b.phi[r])
          continue;
        for (int p : b.pred) {
          if (p >= 0 && !blocks[p].done)
            continue;
          Value *val = p < 0 ? init[r] : blocks[p].out[r];
          BasicBlock *from = p < 0 ? &pre : blocks[p].exit;
          b.phi[r]->addValue(*val, std::string(from->getName()));
        }
      }
    }
  }
};

Trace Lifter::concrete(const std::unordered_map<std::string, uint64_t> &bound) {
  std::unordered_map<const Value *, uint64_t> env;
  auto eval = [&](const Value *v) -> std::optional<uint64_t> {
    if (!v)
      return std::nullopt;
    if (auto *constant = dynamic_cast<const IntConst *>(v)) {
      if (auto *n = constant->getInt())
        return static_cast<uint64_t>(*n);
      return std::nullopt;
    }
    if (auto *input = dynamic_cast<const Input *>(v)) {
      auto it = bound.find(input->getName());
      if (it == bound.end())
        return std::nullopt;
      return it->second;
    }
    if (dynamic_cast<const PoisonValue *>(v) ||
        dynamic_cast<const UndefValue *>(v))
      return std::nullopt;
    auto it = env.find(v);
    if (it == env.end())
      return std::nullopt;
    return it->second;
  };

  uint64_t arch[10]{};
  for (int i = 0; i < 10; ++i) {
    auto v = eval(init[i]);
    if (!v)
      throw std::runtime_error("initial register is not concrete");
    arch[i] = *v;
  }

  Trace trace;
  trace.memory = MemorySummary::Empty;
  trace.producer = Producer::Ok;
  bool halt = false;

  auto file_of = [&]() {
    RegFile file;
    for (int i = 0; i < 10; ++i)
      file.r[i] = Bv64{arch[i]};
    return file;
  };
  auto project = [&](const std::array<Value *, 11> &regs, RegFile &out) {
    for (int i = 0; i < 10; ++i) {
      if (!regs[i] || regs[i]->bits() != 64)
        return false;
      auto v = eval(regs[i]);
      if (!v)
        return false;
      out.r[i] = Bv64{*v};
    }
    return true;
  };
  auto emit_step = [&](SourceEnd &end, StepStatus status) {
    if (halt)
      return;
    end.flushed = true;
    if (!trace.steps.empty() &&
        trace.steps.back().status == StepStatus::Next &&
        std::holds_alternative<std::monostate>(trace.steps.back().pc_after))
      trace.steps.back().pc_after = InsnPc{end.index};
    Step step;
    step.pc.index = end.index;
    step.pc_after = std::monostate{};
    step.before = file_of();
    if (trace.steps.size() >= code.size() + 1)
      status = StepStatus::Incomplete;
    if (status == StepStatus::Ub || status == StepStatus::Unsupported ||
        status == StepStatus::Incomplete) {
      step.status = status;
      step.after = step.before;
      step.pc_after = std::monostate{};
      trace.steps.push_back(step);
      halt = true;
      return;
    }
    if (!project(end.regs, step.after)) {
      step.status = StepStatus::Unsupported;
      step.after = step.before;
      step.pc_after = std::monostate{};
      trace.steps.push_back(step);
      halt = true;
      return;
    }
    step.status = status;
    if (status == StepStatus::Exit) {
      step.pc_after = ExitPc{};
      if (auto *bits = std::get_if<Bv64>(&step.after.r[0]))
        step.return_value = *bits;
      else {
        step.status = StepStatus::Unsupported;
        step.pc_after = std::monostate{};
        halt = true;
      }
    }
    for (int i = 0; i < 10; ++i)
      arch[i] = std::get<Bv64>(step.after.r[i]).bits;
    trace.steps.push_back(step);
  };
  auto stop_unsupported = [&](Instr *ins) {
    for (auto &end : ends) {
      if (!end.flushed && end.after == ins) {
        emit_step(end, StepStatus::Unsupported);
        return;
      }
    }
    Step step;
    step.status = StepStatus::Unsupported;
    step.before = file_of();
    step.after = step.before;
    trace.steps.push_back(step);
    halt = true;
  };
  auto flush_entry = [&](BasicBlock *block) {
    for (auto &end : ends) {
      if (!end.flushed && end.kind == CommitKind::AtEntry && end.block == block)
        emit_step(end, StepStatus::Next);
    }
  };
  auto flush_after = [&](Instr *ins, StepStatus status) {
    for (auto &end : ends) {
      if (!end.flushed && end.kind == CommitKind::AfterInstr && end.after == ins)
        emit_step(end, status);
    }
  };

  BasicBlock *bb = &fn.getEntryBB();
  BasicBlock *from = nullptr;
  int guard = 0;
  while (bb && !halt) {
    if (++guard > static_cast<int>(code.size()) + 8) {
      Step step;
      step.status = StepStatus::Incomplete;
      step.before = file_of();
      step.after = step.before;
      trace.steps.push_back(step);
      break;
    }
    flush_entry(bb);
    bool moved = false;
    for (const auto &ins_ref : bb->instrs()) {
      Instr *ins = const_cast<Instr *>(&ins_ref);
      if (halt)
        break;
      if (auto *phi = dynamic_cast<Phi *>(ins)) {
        std::optional<uint64_t> picked;
        if (from) {
          for (const auto &incoming : phi->getValues()) {
            if (incoming.second == from->getName())
              picked = eval(incoming.first);
          }
        }
        if (!picked) {
          stop_unsupported(ins);
          break;
        }
        env[ins] = *picked;
        flush_after(ins, StepStatus::Next);
      } else if (auto *binop = dynamic_cast<BinOp *>(ins)) {
        auto ops = binop->operands();
        auto lhs = ops.size() == 2 ? eval(ops[0]) : std::nullopt;
        auto rhs = ops.size() == 2 ? eval(ops[1]) : std::nullopt;
        IrOp op = IrOp::Add;
        bool known = true;
        switch (binop->getOp()) {
        case BinOp::Add: op = IrOp::Add; break;
        case BinOp::Sub: op = IrOp::Sub; break;
        case BinOp::And: op = IrOp::And; break;
        case BinOp::UDiv: op = IrOp::UDiv; break;
        case BinOp::SDiv: op = IrOp::SDiv; break;
        default: known = false; break;
        }
        if (!known || !lhs || !rhs) {
          stop_unsupported(ins);
          break;
        }
        auto result = eval_op(op, *lhs, *rhs, binop->bits());
        if (result.kind == IrResultKind::Ub) {
          bool committed = false;
          for (auto &end : ends) {
            if (!end.flushed && end.after == ins) {
              emit_step(end, StepStatus::Ub);
              committed = true;
              break;
            }
          }
          if (!committed)
            stop_unsupported(ins);
          break;
        }
        if (result.kind != IrResultKind::Bits &&
            result.kind != IrResultKind::I1) {
          stop_unsupported(ins);
          break;
        }
        env[ins] = result.bits;
        flush_after(ins, StepStatus::Next);
      } else if (auto *icmp = dynamic_cast<ICmp *>(ins)) {
        auto ops = icmp->operands();
        auto lhs = ops.size() == 2 ? eval(ops[0]) : std::nullopt;
        auto rhs = ops.size() == 2 ? eval(ops[1]) : std::nullopt;
        IrOp op = IrOp::ICmpEq;
        bool known = true;
        switch (icmp->getCond()) {
        case ICmp::EQ: op = IrOp::ICmpEq; break;
        case ICmp::UGT: op = IrOp::ICmpUgt; break;
        default: known = false; break;
        }
        unsigned width = ops.empty() ? 0 : ops[0]->bits();
        if (!known || !lhs || !rhs) {
          stop_unsupported(ins);
          break;
        }
        auto result = eval_op(op, *lhs, *rhs, width);
        if (result.kind != IrResultKind::I1) {
          stop_unsupported(ins);
          break;
        }
        env[ins] = result.bits;
        flush_after(ins, StepStatus::Next);
      } else if (auto *branch = dynamic_cast<Branch *>(ins)) {
        flush_after(ins, StepStatus::Next);
        BasicBlock *dest = nullptr;
        if (auto *cond = branch->getCond()) {
          auto bit = eval(cond);
          if (!bit) {
            stop_unsupported(ins);
            break;
          }
          dest = const_cast<BasicBlock *>(
              (*bit & 1) ? &branch->getTrue() : branch->getFalse());
        } else {
          dest = const_cast<BasicBlock *>(&branch->getTrue());
        }
        if (!dest) {
          stop_unsupported(ins);
          break;
        }
        from = bb;
        bb = dest;
        moved = true;
        break;
      } else if (dynamic_cast<Return *>(ins)) {
        flush_after(ins, StepStatus::Exit);
        halt = true;
        moved = true;
        break;
      } else {
        if (dynamic_cast<MemInstr *>(ins))
          trace.memory = MemorySummary::Changed;
        stop_unsupported(ins);
        break;
      }
    }
    if (!moved && !halt) {
      Step step;
      step.status = StepStatus::Unsupported;
      step.before = file_of();
      step.after = step.before;
      trace.steps.push_back(step);
      break;
    }
  }
  return trace;
}

Trace make_alive_trace(const std::vector<uint8_t> &bytes,
                       const std::vector<std::pair<uint8_t, Bv64>> &inputs,
                       BugFlag bug) {
  auto insns = decode_ebpf(bytes);
  std::vector<std::pair<uint8_t, std::string>> named;
  std::unordered_map<std::string, uint64_t> bound;
  for (auto [reg, value] : inputs) {
    if (reg > 9)
      throw std::runtime_error("input register out of range");
    auto name = "r" + std::to_string(reg);
    named.emplace_back(reg, name);
    bound.emplace(name, value.bits);
  }
  EbTypes types;
  Function fn(types.i64, "ebpf");
  LiftBug lift_bug =
      bug == BugFlag::DivZeroAsUb ? LiftBug::DivZeroAsUb : LiftBug::None;
  Lifter lifter(fn, types, insns, lift_bug);
  lifter.run(named);
  return lifter.concrete(bound);
}

} // namespace

LiftInfo lift_ebpf(IR::Function &fn, EbTypes &types,
                   const std::vector<EbInsn> &code,
                   const std::vector<std::pair<uint8_t, std::string>> &inputs,
                   LiftBug bug) {
  return Lifter(fn, types, code, bug).run(inputs);
}

Trace alive2_trace(const std::vector<uint8_t> &code,
                   const std::vector<std::pair<uint8_t, Bv64>> &inputs,
                   BugFlag bug) {
  return make_alive_trace(code, inputs, bug);
}

