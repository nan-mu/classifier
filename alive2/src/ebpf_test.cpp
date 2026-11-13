#include "ebpf_check.h"
#include "ebpf_ref.h"
#include "ebpf_run.h"
#include "smt/solver.h"
#include "smt/smt.h"

#include <array>
#include <iostream>
#include <random>
#include <string>
#include <vector>

namespace {

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

void decode_spec_example() {
  std::vector<uint8_t> bytes = {0x07, 0x01, 0x00, 0x00, 0x44, 0x33, 0x22, 0x11};
  auto insns = decode_ebpf(bytes);
  expect(insns.size() == 1, "spec example decodes one insn");
  const auto &alu = std::get<EbAlu>(insns[0].op);
  expect(alu.width == EbWidth::W64 && alu.op == EbAlu::Add && alu.dst == 1 &&
             alu.src == EbSrc::Imm && alu.imm == 0x11223344,
         "spec example is alu64 add r1, 0x11223344");
}

void reject_encoding(const char *name, uint8_t opcode, uint8_t dst, uint8_t src,
                     int16_t off, int32_t imm) {
  std::vector<uint8_t> bytes;
  put(bytes, opcode, dst, src, off, imm);
  std::string why;
  try {
    decode_ebpf(bytes);
  } catch (const std::runtime_error &err) {
    why = err.what();
  }
  expect(!why.empty(), std::string(name) + " is rejected");
  if (!why.empty())
    std::cout << "  reason: " << why << "\n";
}

void reject_unknown() {
  std::cout << "\n== unsupported encodings must error, never act as nop ==\n";
  reject_encoding("LDX", 0x61, 0, 1, 0, 0);
  reject_encoding("ST", 0x62, 1, 0, 0, 7);
  reject_encoding("STX", 0x63, 1, 2, 0, 0);
  reject_encoding("LDDW", 0x18, 1, 0, 0, 0);
  reject_encoding("CALL", 0x85, 0, 0, 0, 1);
  reject_encoding("JSET", 0x45, 1, 0, 2, 1);
  reject_encoding("JMP32 JSET", 0x46, 1, 0, 2, 1);
  reject_encoding("byte swap END", 0xd4, 1, 0, 0, 32);
  reject_encoding("MOVSX with immediate", MOV | ALU64, 1, 0, 8, 0);
  reject_encoding("MOVSX offset 32 in ALU32", MOV | X | ALU, 1, 2, 32, 0);
  reject_encoding("MOVSX offset 7", MOV | X | ALU64, 1, 2, 7, 0);
  reject_encoding("DIV offset 2", DIV | X | ALU64, 1, 2, 2, 0);
  reject_encoding("NEG with register source", NEG | X | ALU64, 1, 2, 0, 0);
}

void reject_bad_program() {
  std::vector<uint8_t> bytes;
  put(bytes, JEQ | JMP, 1, 0, 100, 0);
  put(bytes, EXIT | JMP, 0, 0, 0, 0);
  std::string why;
  try {
    execute_ebpf(bytes, {{1, "r1"}}, 0);
  } catch (const std::runtime_error &err) {
    why = err.what();
  }
  expect(!why.empty(), "jump target past the end is rejected");
  if (!why.empty())
    std::cout << "  reason: " << why << "\n";
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

// Back edge is a conditional jump and the exit test sits at the bottom, so the
// CFG differs from loop_prog's top-tested header. r1 == 0 never terminates here.
std::vector<uint8_t> loop_bottom_test_prog() {
  std::vector<uint8_t> c;
  put(c, MOV | ALU64, 0, 0, 0, 0);
  put(c, ADD | ALU64, 0, 0, 0, 2);
  put(c, SUB | ALU64, 1, 0, 0, 1);
  put(c, JNE | JMP, 1, 0, -3, 0);
  put(c, EXIT | JMP, 0, 0, 0, 0);
  return c;
}

std::vector<uint8_t> alu_prog(uint8_t opcode, int16_t offset, int32_t imm) {
  std::vector<uint8_t> c;
  put(c, MOV | X | ALU64, 0, 1, 0, 0);
  put(c, opcode, 0, (opcode & X) ? 2 : 0, offset, imm);
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

struct IsaCase {
  std::string name;
  uint8_t opcode;
  int16_t offset;
  int32_t imm;
  bool jump;
};

// The opcode table from Linux v6.12 instruction-set.rst, not a list of programs
// someone remembered to write. Every accepted encoding gets a row.
std::vector<IsaCase> isa_matrix() {
  std::vector<IsaCase> out;
  struct AluOp {
    const char *name;
    uint8_t code;
    int16_t offset;
    bool reg_only;
    bool imm_only;
  };
  static const AluOp alu[] = {
      {"add", ADD, 0, false, false},   {"sub", SUB, 0, false, false},
      {"mul", MUL, 0, false, false},   {"div", DIV, 0, false, false},
      {"sdiv", DIV, 1, false, false},  {"or", OR, 0, false, false},
      {"and", AND, 0, false, false},   {"lsh", LSH, 0, false, false},
      {"rsh", RSH, 0, false, false},   {"neg", NEG, 0, false, true},
      {"mod", MOD, 0, false, false},   {"smod", MOD, 1, false, false},
      {"xor", XOR, 0, false, false},   {"mov", MOV, 0, false, false},
      {"arsh", ARSH, 0, false, false}, {"movsx8", MOV, 8, true, false},
      {"movsx16", MOV, 16, true, false}, {"movsx32", MOV, 32, true, false},
  };
  for (const auto &a : alu) {
    for (uint8_t cls : {ALU, ALU64}) {
      if (a.offset == 32 && cls == ALU)
        continue;
      for (bool reg : {false, true}) {
        if (a.reg_only && !reg)
          continue;
        if (a.imm_only && reg)
          continue;
        std::vector<int32_t> imms = reg ? std::vector<int32_t>{0}
                                        : std::vector<int32_t>{-1, 0x40000001};
        for (int32_t imm : imms) {
          IsaCase c;
          c.name = std::string(cls == ALU ? "alu32 " : "alu64 ") + a.name +
                   (reg ? " reg" : " imm " + std::to_string(imm));
          c.opcode = static_cast<uint8_t>(a.code | cls | (reg ? X : 0));
          c.offset = a.offset;
          c.imm = imm;
          c.jump = false;
          out.push_back(c);
        }
      }
    }
  }
  struct JmpOp {
    const char *name;
    uint8_t code;
  };
  static const JmpOp jmp[] = {
      {"jeq", JEQ},   {"jgt", JGT},   {"jge", JGE},  {"jne", JNE},
      {"jsgt", JSGT}, {"jsge", JSGE}, {"jlt", JLT},  {"jle", JLE},
      {"jslt", JSLT}, {"jsle", JSLE},
  };
  for (const auto &j : jmp) {
    for (uint8_t cls : {JMP, JMP32}) {
      for (bool reg : {false, true}) {
        std::vector<int32_t> imms = reg ? std::vector<int32_t>{0}
                                        : std::vector<int32_t>{-1, 1};
        for (int32_t imm : imms) {
          IsaCase c;
          c.name = std::string(cls == JMP ? "jmp " : "jmp32 ") + j.name +
                   (reg ? " reg" : " imm " + std::to_string(imm));
          c.opcode = static_cast<uint8_t>(j.code | cls | (reg ? X : 0));
          c.offset = 2;
          c.imm = imm;
          c.jump = true;
          out.push_back(c);
        }
      }
    }
  }
  out.push_back({"jmp ja", JA | JMP, 2, 0, true});
  out.push_back({"jmp32 ja", JA | JMP32, 0, 2, true});
  out.push_back({"jmp exit", EXIT | JMP, 0, 0, true});
  return out;
}

std::vector<uint8_t> case_prog(const IsaCase &c) {
  std::vector<uint8_t> code;
  bool reg = c.opcode & X;
  uint8_t code_field = c.opcode & 0xf0;
  if (!c.jump) {
    put(code, MOV | X | ALU64, 0, 1, 0, 0);
    put(code, c.opcode, 0, reg ? 2 : 0, c.offset, c.imm);
    put(code, EXIT | JMP, 0, 0, 0, 0);
    return code;
  }
  if (code_field == EXIT) {
    put(code, MOV | X | ALU64, 0, 1, 0, 0);
    put(code, EXIT | JMP, 0, 0, 0, 0);
    return code;
  }
  if (code_field == JA) {
    bool imm_form = (c.opcode & 0x07) == JMP32;
    put(code, c.opcode, 0, 0, imm_form ? 0 : c.offset, imm_form ? c.imm : 0);
  } else {
    put(code, c.opcode, 1, reg ? 2 : 0, c.offset, c.imm);
  }
  put(code, MOV | ALU64, 0, 0, 0, 0);
  put(code, EXIT | JMP, 0, 0, 0, 0);
  put(code, MOV | ALU64, 0, 0, 0, 1);
  put(code, EXIT | JMP, 0, 0, 0, 0);
  return code;
}

std::vector<std::pair<uint8_t, std::string>> case_inputs(const IsaCase &c) {
  if (c.jump && (c.opcode & 0xf0) == JA)
    return {};
  std::vector<std::pair<uint8_t, std::string>> inputs = {{1, "r1"}};
  if (c.opcode & X)
    inputs.push_back({2, "r2"});
  return inputs;
}

void check_isa_matrix() {
  std::cout << "\n== per-opcode ISA matrix ==\n";
  auto matrix = isa_matrix();
  std::cout << "matrix cases " << matrix.size() << "\n";
  for (const auto &c : matrix) {
    auto e = execute_ebpf(case_prog(c), case_inputs(c), 0);
    expect_equiv(e, c.name);
    expect_sweep(e, boundary_points(e), c.name);
  }
}

std::vector<uint8_t> random_prog(std::mt19937_64 &rng, unsigned len) {
  static const std::vector<IsaCase> alu = [] {
    std::vector<IsaCase> v;
    for (const auto &c : isa_matrix())
      if (!c.jump)
        v.push_back(c);
    return v;
  }();
  struct Tmpl {
    uint8_t opcode;
    uint8_t dst;
    uint8_t src;
    int16_t off;
    int32_t imm;
  };
  std::vector<Tmpl> body;
  for (unsigned i = 0; i < len; ++i) {
    Tmpl t{};
    bool jump = i + 2 < len && rng() % 5 == 0;
    if (jump) {
      static const uint8_t conds[] = {JEQ, JGT, JGE, JNE, JSGT,
                                      JSGE, JLT, JLE, JSLT, JSLE};
      uint8_t cls = rng() % 2 ? JMP : JMP32;
      bool reg = rng() % 2;
      unsigned target = i + 2 + rng() % (len - i - 1);
      t.opcode = static_cast<uint8_t>(conds[rng() % 10] | cls | (reg ? X : 0));
      t.dst = 1 + rng() % 5;
      t.src = reg ? 1 + rng() % 5 : 0;
      t.off = static_cast<int16_t>(target - i - 1);
      t.imm = reg ? 0 : static_cast<int32_t>(rng());
    } else {
      const auto &pick = alu[rng() % alu.size()];
      t.opcode = pick.opcode;
      t.off = pick.offset;
      t.dst = rng() % 6;
      t.src = (pick.opcode & X) ? 1 + rng() % 5 : 0;
      static const int32_t pool[] = {0, 1, -1, 31, 63, 64, 0x7fffffff,
                                     static_cast<int32_t>(0x80000000u)};
      t.imm = (pick.opcode & X) ? 0
                                : (rng() % 2 ? pool[rng() % 8]
                                             : static_cast<int32_t>(rng()));
    }
    body.push_back(t);
  }
  std::vector<uint8_t> code;
  for (const auto &t : body)
    put(code, t.opcode, t.dst, t.src, t.off, t.imm);
  put(code, MOV | X | ALU64, 0, rng() % 6, 0, 0);
  put(code, EXIT | JMP, 0, 0, 0, 0);
  return code;
}

void check_random_differential(unsigned rounds, uint64_t seed) {
  std::cout << "\n== random differential, seed " << seed << ", " << rounds
            << " programs ==\n";
  std::mt19937_64 rng(seed);
  for (unsigned i = 0; i < rounds; ++i) {
    unsigned len = 3 + rng() % 6;
    auto code = random_prog(rng, len);
    std::vector<std::pair<uint8_t, std::string>> inputs = {
        {1, "r1"}, {2, "r2"}, {3, "r3"}};
    std::string name = "fuzz " + std::to_string(i);
    EbExec e;
    try {
      e = execute_ebpf(code, inputs, 0);
    } catch (const std::runtime_error &err) {
      expect(false, name + " lifted: " + err.what());
      continue;
    }
    expect_equiv(e, name);
    std::vector<std::vector<uint64_t>> points;
    for (unsigned p = 0; p < 24; ++p)
      points.push_back({rng(), rng(), rng()});
    for (uint64_t a : boundary_values())
      points.push_back({a, a, a});
    expect_sweep(e, points, name);
  }
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

void check_loop(const std::vector<uint8_t> &code, const std::string &name,
                bool sample) {
  std::vector<int> covered1;
  std::vector<int> covered4;
  for (unsigned unroll : {1u, 4u}) {
    auto e = execute_ebpf(code, {{1, "r1"}}, unroll);
    if (unroll == 1 && sample)
      print_sample(e);
    std::cout << name << " unroll " << unroll << " covered";
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
      expect(got == want, name + " n=" + std::to_string(n) + " unroll " +
                              std::to_string(unroll));
    }
    (unroll == 1 ? covered1 : covered4) = covered;
  }
  expect(covered1.size() < covered4.size(),
         name + " larger unroll covers more trips");
  expect(!covered4.empty() && covered4.back() < 8,
         name + " some trips stay outside the bound");
}

} // namespace

int main() {
  smt::smt_initializer smt;
  decode_spec_example();
  reject_unknown();
  reject_bad_program();

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

  {
    auto sdiv = alu_prog(DIV | X | ALU64, 1, 0);
    auto e = execute_ebpf(sdiv, {{1, "r1"}, {2, "r2"}}, 0);
    expect_equiv(e, "sdiv64");
    expect_at(e, {{1, 0x8000000000000000ull}, {2, 0xffffffffffffffffull}},
              0x8000000000000000ull, "sdiv64 INT_MIN / -1 wraps to INT_MIN");
    expect_at(e, {{1, 0xfffffffffffffffdull}, {2, 3}},
              0xffffffffffffffffull, "sdiv64 -3 / 3 truncates toward zero");
    expect_at(e, {{1, 7}, {2, 0}}, 0, "sdiv64 zero divisor gives 0");
    auto smod = alu_prog(MOD | X | ALU64, 1, 0);
    auto m = execute_ebpf(smod, {{1, "r1"}, {2, "r2"}}, 0);
    expect_equiv(m, "smod64");
    expect_at(m, {{1, 0x8000000000000000ull}, {2, 0xffffffffffffffffull}}, 0,
              "smod64 INT_MIN % -1 is 0");
    expect_at(m, {{1, 0xfffffffffffffff3ull}, {2, 3}},
              0xffffffffffffffffull, "smod64 -13 % 3 is -1 truncated");
    expect_at(m, {{1, 7}, {2, 0}}, 7, "smod64 zero divisor keeps dst");
  }
  {
    // Both operands are constants here, so Alive2's expr::sdiv constant folder
    // is in play. Symbolic-register cases never reach it.
    std::vector<uint8_t> c;
    put(c, MOV | ALU64, 0, 0, 0, 1);
    put(c, LSH | ALU64, 0, 0, 0, 63);
    put(c, DIV | ALU64, 0, 0, 1, -1);
    put(c, EXIT | JMP, 0, 0, 0, 0);
    auto e = execute_ebpf(c, {}, 0);
    expect_equiv(e, "sdiv64 constant INT_MIN / -1");
    expect_at(e, {}, 0x8000000000000000ull, "sdiv64 constant INT_MIN / -1");
    std::vector<uint8_t> m;
    put(m, MOV | ALU64, 0, 0, 0, 1);
    put(m, LSH | ALU64, 0, 0, 0, 63);
    put(m, MOD | ALU64, 0, 0, 1, -1);
    put(m, EXIT | JMP, 0, 0, 0, 0);
    auto f = execute_ebpf(m, {}, 0);
    expect_equiv(f, "smod64 constant INT_MIN % -1");
    expect_at(f, {}, 0, "smod64 constant INT_MIN % -1");
  }
  {
    auto e = execute_ebpf(alu_prog(MOV | X | ALU64, 8, 0),
                          {{1, "r1"}, {2, "r2"}}, 0);
    expect_equiv(e, "movsx8");
    expect_at(e, {{1, 0}, {2, 0xff}}, 0xffffffffffffffffull,
              "movsx8 0xff sign extends to -1");
    expect_at(e, {{1, 0}, {2, 0x7f}}, 0x7f, "movsx8 0x7f stays positive");
  }

  check_isa_matrix();
  check_random_differential(120, 0x5eed1234ull);

  std::cout << "\n== sample conditional program ==\n";
  {
    auto e = execute_ebpf(branch_prog(), {{1, "r1"}}, 0);
    print_sample(e);
    expect_equiv(e, "branch");
    expect_at(e, {{1, 10}}, 9, "branch x == 10");
    expect_at(e, {{1, 11}}, 12, "branch x == 11");
  }

  std::cout << "\n== bounded loop, top-tested header ==\n";
  check_loop(loop_prog(), "loop", true);
  std::cout << "\n== bounded loop, bottom-tested back edge ==\n";
  check_loop(loop_bottom_test_prog(), "loop-bottom", false);

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
      {"sdiv overflow as ub", alu_prog(DIV | X | ALU64, 1, 0),
       {{1, "r1"}, {2, "r2"}}, LiftBug::SdivOverflowAsUb},
      {"shift without mask", alu_prog(LSH | X | ALU64, 0, 0),
       {{1, "r1"}, {2, "r2"}}, LiftBug::ShiftWithoutMask},
      {"movsx as zext", alu_prog(MOV | X | ALU64, 8, 0),
       {{1, "r1"}, {2, "r2"}}, LiftBug::MovsxAsZext},
      {"imm without sign extend", alu_prog(SUB | ALU64, 0, -1), {{1, "r1"}},
       LiftBug::ImmNoSignExtend},
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
