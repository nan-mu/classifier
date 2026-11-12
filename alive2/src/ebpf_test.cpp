#include "ebpf_ref.h"
#include "ebpf_run.h"
#include "smt/solver.h"
#include "smt/smt.h"

#include <array>
#include <iostream>
#include <string>
#include <vector>

namespace {

int g_failures = 0;

constexpr uint8_t ALU = 0x04;
constexpr uint8_t JMP = 0x05;
constexpr uint8_t JMP32 = 0x06;
constexpr uint8_t ALU64 = 0x07;
constexpr uint8_t X = 0x08;
constexpr uint8_t ADD = 0x00;
constexpr uint8_t SUB = 0x10;
constexpr uint8_t MUL = 0x20;
constexpr uint8_t DIV = 0x30;
constexpr uint8_t OR = 0x40;
constexpr uint8_t AND = 0x50;
constexpr uint8_t LSH = 0x60;
constexpr uint8_t RSH = 0x70;
constexpr uint8_t NEG = 0x80;
constexpr uint8_t MOD = 0x90;
constexpr uint8_t XOR = 0xa0;
constexpr uint8_t MOV = 0xb0;
constexpr uint8_t ARSH = 0xc0;
constexpr uint8_t JA = 0x00;
constexpr uint8_t JEQ = 0x10;
constexpr uint8_t JGT = 0x20;
constexpr uint8_t JGE = 0x30;
constexpr uint8_t JNE = 0x50;
constexpr uint8_t JSGT = 0x60;
constexpr uint8_t JSGE = 0x70;
constexpr uint8_t EXIT = 0x90;
constexpr uint8_t JLT = 0xa0;
constexpr uint8_t JLE = 0xb0;
constexpr uint8_t JSLT = 0xc0;
constexpr uint8_t JSLE = 0xd0;

const char *answer_name(const smt::Result &r) {
  if (r.isUnsat())
    return "UNSAT";
  if (r.isSat())
    return "SAT";
  if (r.isTimeout())
    return "TIMEOUT";
  if (r.isInvalid())
    return "INVALID";
  if (r.isSkip())
    return "SKIP";
  return "ERROR";
}

void expect(bool cond, const std::string &name) {
  if (!cond) {
    std::cerr << "FAIL " << name << "\n";
    ++g_failures;
  } else {
    std::cout << "PASS " << name << "\n";
  }
}

smt::Result check(const smt::expr &e, const std::string &name, bool want_unsat) {
  auto r = smt::check_expr(e, name.c_str(), true);
  bool ok = want_unsat ? r.isUnsat() : r.isSat();
  std::cout << (ok ? "PASS " : "FAIL ") << name << " " << answer_name(r) << "\n";
  if (!ok) {
    ++g_failures;
    if (r.isSat())
      std::cout << r.getModel() << "\n";
    else if (!r.isUnsat())
      std::cout << "reason " << r.getReason() << "\n";
  }
  return r;
}

void put(std::vector<uint8_t> &o, uint8_t op, uint8_t dst, uint8_t src, int16_t off,
         int32_t imm) {
  uint32_t u = static_cast<uint32_t>(imm);
  uint16_t d = static_cast<uint16_t>(off);
  o.insert(o.end(), {op, static_cast<uint8_t>((src << 4) | dst),
                     static_cast<uint8_t>(d & 0xff), static_cast<uint8_t>(d >> 8),
                     static_cast<uint8_t>(u & 0xff), static_cast<uint8_t>((u >> 8) & 0xff),
                     static_cast<uint8_t>((u >> 16) & 0xff),
                     static_cast<uint8_t>((u >> 24) & 0xff)});
}

smt::expr input_ok(const EbExec &e) {
  smt::expr ok = true;
  for (const auto &[reg, name] : e.inputs) {
    (void)reg;
    auto undef = smt::expr::mkVar(("isundef_" + name).c_str(), 1);
    auto np = smt::expr::mkBoolVar(("np_" + name).c_str());
    ok &= np && undef == 0;
  }
  return ok;
}

std::array<smt::expr, 11> sym_regs(const EbExec &e) {
  std::array<smt::expr, 11> regs;
  for (auto &r : regs)
    r = smt::expr::mkUInt(0, 64);
  for (const auto &[reg, name] : e.inputs)
    regs[reg] = smt::expr::mkVar(name.c_str(), 64);
  return regs;
}

void expect_equiv(const EbExec &e, const std::string &name) {
  auto ref = interpret_ebpf_sym(e.insns, sym_regs(e), 8);
  auto ok = input_ok(e);
  auto mismatch = ok && ((e.returned != ref.returns) ||
                         (e.returned && e.value != ref.r0) ||
                         (e.returned && !e.non_poison));
  check(mismatch, name + " equivalent to reference", true);
}

void expect_at(const EbExec &e, const std::vector<std::pair<uint8_t, uint64_t>> &env,
               uint64_t want, const std::string &name) {
  ConcreteRegs regs;
  auto ok = input_ok(e);
  smt::expr guard = ok;
  for (auto [reg, val] : env) {
    regs.r[reg] = val;
    auto sym = smt::expr::mkVar(e.inputs.at(0).second.c_str(), 64);
    for (const auto &[ireg, iname] : e.inputs) {
      if (ireg == reg)
        sym = smt::expr::mkVar(iname.c_str(), 64);
    }
    guard &= sym == smt::expr::mkUInt(val, 64);
  }
  uint64_t concrete = interpret_ebpf(e.insns, regs);
  expect(concrete == want, name + " concrete reference");
  check(guard && !e.returned, name + " alive returns", true);
  check(guard && e.value != smt::expr::mkUInt(want, 64), name + " alive value", true);
}

void decode_spec_example() {
  std::vector<uint8_t> bytes = {0x07, 0x01, 0x00, 0x00, 0x44, 0x33, 0x22, 0x11};
  auto insns = decode_ebpf(bytes);
  expect(insns.size() == 1, "spec example decodes one insn");
  const auto &alu = std::get<EbAlu>(insns[0].op);
  expect(alu.width == EbWidth::W64 && alu.op == EbAlu::Add && alu.dst == 1 &&
             alu.src == EbSrc::Imm && alu.imm == 0x11223344,
         "spec example is alu64 add r1, 0x11223344");
}

void reject_unknown() {
  std::vector<uint8_t> bytes = {0x61, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};
  bool threw = false;
  try {
    decode_ebpf(bytes);
  } catch (const std::runtime_error &) {
    threw = true;
  }
  expect(threw, "LDX is rejected");
}

std::vector<uint8_t> mul_prog() {
  std::vector<uint8_t> c;
  put(c, MOV | X | ALU64, 0, 1, 0, 0);
  put(c, ADD | ALU64, 0, 0, 0, 3);
  put(c, MUL | X | ALU64, 0, 2, 0, 0);
  put(c, EXIT | JMP, 0, 0, 0, 0);
  return c;
}

std::vector<uint8_t> alu32_prog() {
  std::vector<uint8_t> c;
  put(c, MOV | X | ALU64, 0, 1, 0, 0);
  put(c, ADD | ALU, 0, 0, 0, 1);
  put(c, EXIT | JMP, 0, 0, 0, 0);
  return c;
}

std::vector<uint8_t> div_prog() {
  std::vector<uint8_t> c;
  put(c, MOV | X | ALU64, 0, 1, 0, 0);
  put(c, DIV | X | ALU64, 0, 2, 0, 0);
  put(c, EXIT | JMP, 0, 0, 0, 0);
  return c;
}

std::vector<uint8_t> mod_prog() {
  std::vector<uint8_t> c;
  put(c, MOV | X | ALU64, 0, 1, 0, 0);
  put(c, MOD | X | ALU64, 0, 2, 0, 0);
  put(c, EXIT | JMP, 0, 0, 0, 0);
  return c;
}

std::vector<uint8_t> mod32_prog() {
  std::vector<uint8_t> c;
  put(c, MOV | X | ALU64, 0, 1, 0, 0);
  put(c, MOD | X | ALU, 0, 2, 0, 0);
  put(c, EXIT | JMP, 0, 0, 0, 0);
  return c;
}

std::vector<uint8_t> shift_prog(uint8_t op, bool reg) {
  std::vector<uint8_t> c;
  put(c, MOV | X | ALU64, 0, 1, 0, 0);
  if (reg)
    put(c, op | X | ALU64, 0, 2, 0, 0);
  else
    put(c, op | ALU64, 0, 0, 0, 4);
  put(c, EXIT | JMP, 0, 0, 0, 0);
  return c;
}

std::vector<uint8_t> branch_prog() {
  std::vector<uint8_t> c;
  put(c, JGT | JMP, 1, 0, 3, 10);
  put(c, MOV | X | ALU64, 0, 1, 0, 0);
  put(c, SUB | ALU64, 0, 0, 0, 1);
  put(c, JA | JMP, 0, 0, 2, 0);
  put(c, MOV | X | ALU64, 0, 1, 0, 0);
  put(c, ADD | ALU64, 0, 0, 0, 1);
  put(c, EXIT | JMP, 0, 0, 0, 0);
  return c;
}

std::vector<uint8_t> signed_prog() {
  std::vector<uint8_t> c;
  put(c, JSGT | JMP, 1, 0, 2, 0);
  put(c, MOV | ALU64, 0, 0, 0, 0);
  put(c, JA | JMP, 0, 0, 1, 0);
  put(c, MOV | ALU64, 0, 0, 0, 1);
  put(c, EXIT | JMP, 0, 0, 0, 0);
  return c;
}

std::vector<uint8_t> unsigned_prog() {
  std::vector<uint8_t> c;
  put(c, JGT | JMP, 1, 0, 2, 0);
  put(c, MOV | ALU64, 0, 0, 0, 0);
  put(c, JA | JMP, 0, 0, 1, 0);
  put(c, MOV | ALU64, 0, 0, 0, 1);
  put(c, EXIT | JMP, 0, 0, 0, 0);
  return c;
}

std::vector<uint8_t> loop_prog() {
  std::vector<uint8_t> c;
  put(c, MOV | ALU64, 0, 0, 0, 0);
  put(c, JEQ | JMP, 1, 0, 3, 0);
  put(c, ADD | ALU64, 0, 0, 0, 1);
  put(c, SUB | ALU64, 1, 0, 0, 1);
  put(c, JA | JMP, 0, 0, -4, 0);
  put(c, EXIT | JMP, 0, 0, 0, 0);
  return c;
}

struct OpCase {
  const char *name;
  uint8_t op;
  bool reg;
  uint64_t dst;
  uint64_t src;
  uint64_t want;
};

std::vector<uint8_t> op_case_prog(const OpCase &c) {
  std::vector<uint8_t> code;
  uint8_t opcode = static_cast<uint8_t>(c.op | (c.reg ? X : 0));
  int32_t imm = static_cast<int32_t>(static_cast<uint32_t>(c.src));
  uint8_t cls = static_cast<uint8_t>(opcode & 0x07);
  if (cls == JMP || cls == JMP32) {
    put(code, opcode, 1, c.reg ? 2 : 0, 2, c.reg ? 0 : imm);
    put(code, MOV | ALU64, 0, 0, 0, 0);
    put(code, EXIT | JMP, 0, 0, 0, 0);
    put(code, MOV | ALU64, 0, 0, 0, 1);
    put(code, EXIT | JMP, 0, 0, 0, 0);
    return code;
  }
  put(code, MOV | X | ALU64, 0, 1, 0, 0);
  put(code, opcode, 0, c.reg ? 2 : 0, 0, c.reg ? 0 : imm);
  put(code, EXIT | JMP, 0, 0, 0, 0);
  return code;
}

void check_op_cases() {
  constexpr uint64_t neg1 = 0xffffffffffffffffull;
  static const OpCase cases[] = {
      {"and reg", AND | ALU64, true, neg1, 0x0f0f0f0f0f0f0f0full, 0x0f0f0f0f0f0f0f0full},
      {"or reg", OR | ALU64, true, 0xf0f0f0f0f0f0f0f0ull, 0x0f0f0f0f0f0f0f0full, neg1},
      {"xor reg", XOR | ALU64, true, neg1, 0x0f0f0f0f0f0f0f0full, 0xf0f0f0f0f0f0f0f0ull},
      {"and imm", AND | ALU64, false, 0xffffffff00000000ull, 0xffffffffull,
       0xffffffff00000000ull},
      {"or imm", OR | ALU64, false, 0x100000000ull, 0xffffffffull, neg1},
      {"xor imm", XOR | ALU64, false, neg1, 1, 0xfffffffffffffffeull},
      {"jne taken", JNE | JMP, false, neg1, 0, 1},
      {"jne equal", JNE | JMP, false, 0, 0, 0},
      {"jne reg", JNE | JMP, true, 5, 5, 0},
      {"jlt", JLT | JMP, false, neg1, 0, 0},
      {"jslt", JSLT | JMP, false, neg1, 0, 1},
      {"jle", JLE | JMP, false, neg1, 0, 0},
      {"jsle", JSLE | JMP, false, neg1, 0, 1},
      {"jge", JGE | JMP, false, neg1, 0, 1},
      {"jsge", JSGE | JMP, false, neg1, 0, 0},
      {"jne32", JNE | JMP32, false, 0x100000000ull, 0, 0},
      {"jlt32", JLT | JMP32, false, neg1, 0, 0},
      {"jslt32", JSLT | JMP32, false, neg1, 0, 1},
      {"jle32", JLE | JMP32, false, neg1, 0, 0},
      {"jsle32", JSLE | JMP32, false, neg1, 0, 1},
      {"jge32", JGE | JMP32, false, neg1, 0, 1},
      {"jsge32", JSGE | JMP32, false, neg1, 0, 0},
      // Low 32 bits of 0x1ffffffff are 0xffffffff, and that half is >= 1, so JGE32
      // is taken. The other arm returns 0, so a 64-bit compare is a different predicate.
      {"jge32 trunc", JGE | JMP32, false, 0x1ffffffffull, 1, 1},
  };
  for (const auto &c : cases) {
    std::vector<std::pair<uint8_t, std::string>> inputs = {{1, "r1"}};
    if (c.reg)
      inputs.push_back({2, "r2"});
    auto e = execute_ebpf(op_case_prog(c), inputs, 0);
    expect_equiv(e, c.name);
    std::vector<std::pair<uint8_t, uint64_t>> env = {{1, c.dst}};
    if (c.reg)
      env.push_back({2, c.src});
    expect_at(e, env, c.want, c.name);
  }
}

void print_sample(const EbExec &e) {
  std::cout << "Decoded eBPF instructions\n" << e.decoded;
  std::cout << "Control-flow structure\n" << e.cfg;
  std::cout << "Generated Alive2 IR\n" << e.ir;
  std::cout << "Symbolic return expression\n" << e.value << "\n";
  std::cout << "non-poison " << e.non_poison << "\n";
  std::cout << "Path / definedness conditions\n" << e.defined << "\n";
  std::cout << "return domain " << e.returned << "\n";
  std::cout << "Memory summary\n" << e.memory;
}

bool returns_at(const EbExec &e, uint64_t n) {
  auto r1 = smt::expr::mkVar("r1", 64);
  auto mismatch = input_ok(e) && r1 == smt::expr::mkUInt(n, 64) && !e.returned;
  auto result = smt::check_expr(mismatch, "loop-return", true);
  if (!result.isUnsat() && !result.isSat())
    throw std::runtime_error(std::string("loop return query ") + answer_name(result));
  return result.isUnsat();
}

uint64_t value_at(const EbExec &e, uint64_t n) {
  auto r1 = smt::expr::mkVar("r1", 64);
  smt::Solver solver;
  solver.add(input_ok(e) && r1 == smt::expr::mkUInt(n, 64) && e.returned);
  auto result = solver.check("loop-value", true);
  if (!result.isSat())
    throw std::runtime_error("loop value query did not return SAT");
  return result.getModel().getUInt(e.value);
}

} // namespace

int main() {
  smt::smt_initializer smt;
  decode_spec_example();
  reject_unknown();

  {
    auto e = execute_ebpf(mul_prog(), {{1, "r1"}, {2, "r2"}}, 0);
    expect_equiv(e, "mul");
    expect_at(e, {{1, 5}, {2, 7}}, 56, "mul 5,7");
    expect_at(e, {{1, 0xffffffffffffffffull}, {2, 2}}, 4, "mul (max+3)*2 wraps to 4");
  }
  {
    std::vector<uint8_t> clang_w0_add = {
        0xbf, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00,
        0x01, 0x00, 0x00, 0x00, 0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};
    expect(alu32_prog() == clang_w0_add,
           "alu32 bytes match clang -target bpf for (unsigned)(x + 1)");
    auto e = execute_ebpf(alu32_prog(), {{1, "r1"}}, 0);
    expect_equiv(e, "alu32 add");
    expect_at(e, {{1, 0x1ffffffffull}}, 0, "alu32 clears high bits");
  }
  {
    auto e = execute_ebpf(div_prog(), {{1, "r1"}, {2, "r2"}}, 0);
    expect_equiv(e, "div64");
    expect_at(e, {{1, 7}, {2, 2}}, 3, "div 7/2");
    expect_at(e, {{1, 7}, {2, 0}}, 0, "div zero");
  }
  {
    std::vector<uint8_t> c;
    put(c, MOV | ALU64, 1, 0, 0, 1);
    put(c, LSH | ALU64, 1, 0, 0, 32);
    put(c, MOV | X | ALU64, 0, 1, 0, 0);
    put(c, DIV | ALU64, 0, 0, 0, -1);
    put(c, EXIT | JMP, 0, 0, 0, 0);
    auto e = execute_ebpf(c, {}, 0);
    expect_equiv(e, "div64 imm -1");
    expect_at(e, {}, 0, "div64 imm -1 is the unsigned all-ones divisor");
  }
  {
    auto e = execute_ebpf(mod_prog(), {{1, "r1"}, {2, "r2"}}, 0);
    expect_equiv(e, "mod64");
    expect_at(e, {{1, 7}, {2, 3}}, 1, "mod 7%3");
    expect_at(e, {{1, 7}, {2, 0}}, 7, "mod zero keeps dst");
  }
  {
    auto e = execute_ebpf(mod32_prog(), {{1, "r1"}, {2, "r2"}}, 0);
    expect_equiv(e, "mod32");
    expect_at(e, {{1, 0x1ffffffffull}, {2, 0}}, 0xffffffffull, "mod32 zero clears high");
  }
  {
    auto e = execute_ebpf(shift_prog(LSH, true), {{1, "r1"}, {2, "r2"}}, 0);
    expect_equiv(e, "lsh mask");
    expect_at(e, {{1, 1}, {2, 127}}, 1ull << 63, "lsh 127 masks to 63");
  }
  {
    auto e = execute_ebpf(shift_prog(ARSH, false), {{1, "r1"}}, 0);
    expect_equiv(e, "arsh");
    expect_at(e, {{1, 0x8000000000000000ull}}, 0xf800000000000000ull, "arsh sign fill");
  }
  {
    auto e = execute_ebpf(shift_prog(RSH, false), {{1, "r1"}}, 0);
    expect_equiv(e, "rsh");
    expect_at(e, {{1, 0x8000000000000000ull}}, 0x0800000000000000ull, "rsh zero fill");
  }
  {
    std::vector<uint8_t> c;
    put(c, MOV | ALU64, 0, 0, 0, 1);
    put(c, NEG | ALU64, 0, 0, 0, 0);
    put(c, EXIT | JMP, 0, 0, 0, 0);
    auto e = execute_ebpf(c, {}, 0);
    expect_equiv(e, "neg");
    expect_at(e, {}, 0xffffffffffffffffull, "neg 1");
  }
  {
    auto e = execute_ebpf(signed_prog(), {{1, "r1"}}, 0);
    expect_equiv(e, "jsgt");
    expect_at(e, {{1, 0xffffffffffffffffull}}, 0, "jsgt -1 is not greater than 0");
    expect_at(e, {{1, 1}}, 1, "jsgt 1 is greater than 0");
  }
  {
    auto e = execute_ebpf(unsigned_prog(), {{1, "r1"}}, 0);
    expect_equiv(e, "jgt");
    expect_at(e, {{1, 0xffffffffffffffffull}}, 1, "jgt -1 is greater than 0 unsigned");
  }

  check_op_cases();

  std::cout << "\n== sample conditional program ==\n";
  {
    auto e = execute_ebpf(branch_prog(), {{1, "r1"}}, 0);
    print_sample(e);
    expect_equiv(e, "branch");
    expect_at(e, {{1, 10}}, 9, "branch x == 10");
    expect_at(e, {{1, 11}}, 12, "branch x == 11");
  }

  std::cout << "\n== bounded loop ==\n";
  auto loop = loop_prog();
  std::vector<int> covered1;
  std::vector<int> covered4;
  for (unsigned unroll : {1u, 4u}) {
    auto e = execute_ebpf(loop, {{1, "r1"}}, unroll);
    if (unroll == 1)
      print_sample(e);
    std::cout << "unroll " << unroll << " covered";
    std::vector<int> covered;
    for (int n = 0; n <= 8; ++n) {
      if (!returns_at(e, n))
        continue;
      covered.push_back(n);
      std::cout << " " << n;
    }
    std::cout << "\n";
    for (int n : covered) {
      uint64_t got = value_at(e, n);
      ConcreteRegs regs;
      regs.r[1] = static_cast<uint64_t>(n);
      uint64_t want = interpret_ebpf(e.insns, regs);
      expect(got == want, "loop n=" + std::to_string(n) + " unroll " +
                              std::to_string(unroll));
    }
    (unroll == 1 ? covered1 : covered4) = covered;
  }
  expect(covered1.size() < covered4.size(), "larger unroll covers more trips");
  expect(!covered4.empty() && covered4.back() < 8, "some trips stay outside the bound");

  std::cout << "\n== mutation tests ==\n";
  struct Mut {
    const char *name;
    std::vector<uint8_t> code;
    std::vector<std::pair<uint8_t, std::string>> inputs;
    LiftBug bug;
  };
  Mut muts[] = {
      {"add as sub", mul_prog(), {{1, "r1"}, {2, "r2"}}, LiftBug::AddAsSub},
      {"alu32 as alu64", alu32_prog(), {{1, "r1"}}, LiftBug::Alu32AsAlu64},
      {"div zero as ub", div_prog(), {{1, "r1"}, {2, "r2"}}, LiftBug::DivZeroAsUb},
      {"bad jump", branch_prog(), {{1, "r1"}}, LiftBug::JumpPlusOne},
  };
  for (const auto &mut : muts) {
    auto e = execute_ebpf(mut.code, mut.inputs, 0, mut.bug);
    auto ref = interpret_ebpf_sym(e.insns, sym_regs(e), 8);
    auto mismatch = input_ok(e) && ((e.returned != ref.returns) ||
                                    (e.returned && e.value != ref.r0));
    check(mismatch, std::string(mut.name) + " is caught", false);
  }

  if (g_failures) {
    std::cerr << g_failures << " checks failed\n";
    return 1;
  }
  std::cout << "\nall eBPF checks passed\n";
  return 0;
}
