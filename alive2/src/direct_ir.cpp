#include "ir/constant.h"
#include "ir/function.h"
#include "ir/globals.h"
#include "ir/instr.h"
#include "ir/state.h"
#include "ir/type.h"
#include "smt/expr.h"
#include "smt/solver.h"
#include "smt/smt.h"
#include "util/config.h"
#include "util/symexec.h"

#include <cstdlib>
#include <iostream>
#include <string>

using namespace IR;

namespace {

int g_failures = 0;

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

smt::Result check(const smt::expr &e, const char *name) {
  auto r = smt::check_expr(e, name, true);
  std::cout << "Solver check " << name << " " << answer_name(r) << "\n";
  if (r.isSat())
    std::cout << r.getModel() << "\n";
  if (!r.isSat() && !r.isUnsat())
    std::cout << "reason " << r.getReason() << "\n";
  return r;
}

void expect_unsat(const smt::expr &e, const char *name) {
  auto r = check(e, name);
  if (!r.isUnsat()) {
    std::cerr << "FAIL " << name << " expected UNSAT\n";
    ++g_failures;
  }
}

void expect_sat(const smt::expr &e, const char *name) {
  auto r = smt::check_expr(e, name, true);
  std::cout << "Solver check " << name << " " << answer_name(r) << "\n";
  if (!r.isSat()) {
    std::cerr << "FAIL " << name << " expected SAT\n";
    if (!r.isUnsat())
      std::cout << "reason " << r.getReason() << "\n";
    ++g_failures;
  }
}

smt::expr defined_input(const char *name) {
  auto undef = smt::expr::mkVar((std::string("isundef_") + name).c_str(), 1);
  auto np = smt::expr::mkBoolVar((std::string("np_") + name).c_str());
  return np && undef == 0;
}

void configure_pure_alu() {
  num_locals_src = 0;
  num_locals_tgt = 0;
  num_nonlocals = 0;
  num_nonlocals_src = 0;
  num_globals_src = 0;
  num_ptrinputs = 0;
  has_fncall = false;
  has_alloca = false;
  has_null_block = false;
  has_int2ptr = false;
  has_nocapture = false;
  has_initializes_attr = false;
  does_int_load = false;
  does_int_store = false;
  does_ptr_load = false;
  does_ptr_store = false;
  observes_addresses = false;
}

void configure_one_alloca() {
  configure_pure_alu();
  num_locals_src = 1;
  num_nonlocals = 1;
  num_nonlocals_src = 1;
  has_alloca = true;
  does_int_load = true;
  does_int_store = true;
  bits_byte = 8;
  bits_poison_per_byte = 1;
  bits_for_bid = 2;
  bits_for_offset = 16;
  bits_size_t = 16;
  bits_ptr_address = 16;
  bits_program_pointer = 64;
  little_endian = true;
}

struct Built {
  Function fn;
  State state;
  State::ValTy ret;

  Built(Type &ty, const char *name)
      : fn(ty, name), state(fn, true), ret() {}
};

void exec(Built &b) {
  std::cout << "Alive2 IR\n" << b.fn << "\n";
  util::sym_exec(b.state);
  b.ret = b.state.returnVal();
  std::cout << "Symbolic return expression\n" << b.ret.val << "\n";
  std::cout << "Path conditions\nreturn domain " << b.ret.return_domain
            << "\n";
  std::cout << "Definedness / UB conditions\nfunction domain " << b.ret.domain
            << "\n";
}

Value &constant(Function &fn, Type &ty, int64_t v) {
  auto c = std::make_unique<IntConst>(ty, v);
  Value &ref = *c;
  fn.addConstant(std::move(c));
  return ref;
}

Value &input(Function &fn, Type &ty, const char *name) {
  auto in = std::make_unique<Input>(ty, name);
  Value &ref = *in;
  fn.addInput(std::move(in));
  return ref;
}

void arithmetic(IntType &i32) {
  std::cout << "\n== arithmetic x + y * 3 ==\n";
  State::resetGlobals();
  configure_pure_alu();
  Built b(i32, "add_mul");
  auto &x = input(b.fn, i32, "x");
  auto &y = input(b.fn, i32, "y");
  auto &three = constant(b.fn, i32, 3);
  auto &entry = b.fn.getBB("%entry");
  entry.addInstr(std::make_unique<BinOp>(i32, "%mul", y, three, BinOp::Mul));
  entry.addInstr(std::make_unique<BinOp>(i32, "%sum", x, entry.back(), BinOp::Add));
  entry.addInstr(std::make_unique<Return>(i32, entry.back()));

  std::cout << "Input symbols\n" << x.getName() << " " << y.getName() << "\n";
  exec(b);
  std::cout << "Memory summary\nnone\n";

  smt::expr xv = b.state[x].value;
  smt::expr yv = b.state[y].value;
  smt::expr expected = xv + (yv * smt::expr::mkUInt(3, 32));
  smt::expr inputs = defined_input("x") && defined_input("y");
  smt::expr defined = b.ret.domain();
  smt::expr returned = b.ret.return_domain;

  expect_unsat(inputs && !defined, "arith has no UB on bitvector inputs");
  expect_unsat(inputs && !returned, "arith returns on bitvector inputs");
  expect_unsat(inputs && !b.ret.val.non_poison, "arith result is not poison");
  expect_unsat(inputs && b.ret.val.value != expected, "arith matches x + y * 3");
  expect_sat(inputs && b.ret.val.value != (xv + (yv * smt::expr::mkUInt(4, 32))),
             "arith harness rejects x + y * 4");

  smt::expr overflow_x = smt::expr::mkUInt(0xffffffffu, 32);
  smt::expr overflow_y = smt::expr::mkUInt(1, 32);
  expect_unsat(xv == overflow_x && yv == overflow_y && b.ret.val.value !=
                                                           smt::expr::mkUInt(2, 32),
               "arith overflow wraps to 2");
}

void branch(IntType &i32, IntType &i1) {
  std::cout << "\n== branch x > 10 ==\n";
  State::resetGlobals();
  configure_pure_alu();
  Built b(i32, "branch");
  auto &x = input(b.fn, i32, "x");
  auto &ten = constant(b.fn, i32, 10);
  auto &one = constant(b.fn, i32, 1);
  auto &entry = b.fn.getBB("%entry");
  auto &then_bb = b.fn.getBB("%then");
  auto &else_bb = b.fn.getBB("%else");
  auto &merge = b.fn.getBB("%merge");

  entry.addInstr(std::make_unique<ICmp>(i1, "%c", ICmp::UGT, x, ten));
  entry.addInstr(std::make_unique<Branch>(entry.back(), then_bb, else_bb));
  then_bb.addInstr(std::make_unique<BinOp>(i32, "%inc", x, one, BinOp::Add));
  then_bb.addInstr(std::make_unique<Branch>(merge));
  else_bb.addInstr(std::make_unique<BinOp>(i32, "%dec", x, one, BinOp::Sub));
  else_bb.addInstr(std::make_unique<Branch>(merge));

  auto phi = std::make_unique<Phi>(i32, "%r");
  phi->addValue(then_bb.at(0), "%then");
  phi->addValue(else_bb.at(0), "%else");
  merge.addInstr(std::move(phi));
  merge.addInstr(std::make_unique<Return>(i32, merge.at(0)));

  std::cout << "Input symbols\n" << x.getName() << "\n";
  exec(b);
  std::cout << "entry -> then " << b.state.getJumpCond(entry, then_bb) << "\n";
  std::cout << "entry -> else " << b.state.getJumpCond(entry, else_bb) << "\n";
  std::cout << "Memory summary\nnone\n";

  smt::expr xv = b.state[x].value;
  smt::expr expected =
      smt::expr::mkIf(xv.ugt(10), xv + smt::expr::mkUInt(1, 32),
                      xv - smt::expr::mkUInt(1, 32));
  smt::expr inputs = defined_input("x");
  expect_unsat(inputs && !b.ret.domain(), "branch has no UB on bitvector inputs");
  expect_unsat(inputs && b.ret.val.value != expected,
               "branch matches ite(x > 10, x + 1, x - 1)");
  expect_sat(inputs && b.ret.val.value !=
                           smt::expr::mkIf(xv.ugt(10), xv - smt::expr::mkUInt(1, 32),
                                           xv + smt::expr::mkUInt(1, 32)),
             "branch harness rejects swapped arms");
}

void memory(IntType &i32, PtrType &ptr) {
  std::cout << "\n== memory store then load ==\n";
  State::resetGlobals();
  configure_one_alloca();
  Built b(i32, "memory");
  auto &x = input(b.fn, i32, "x");
  auto &four = constant(b.fn, i32, 4);
  auto &entry = b.fn.getBB("%entry");
  entry.addInstr(std::make_unique<Alloc>(ptr, "%p", four, nullptr, 4));
  entry.addInstr(std::make_unique<Store>(entry.back(), x, 4));
  entry.addInstr(std::make_unique<Load>(i32, "%v", entry.at(0), 4));
  entry.addInstr(std::make_unique<Return>(i32, entry.back()));

  std::cout << "Input symbols\n" << x.getName() << "\n";
  exec(b);
  std::cout << "Memory summary\n" << b.state.returnMemory() << "\n";

  smt::expr xv = b.state[x].value;
  smt::expr inputs = defined_input("x");
  expect_unsat(inputs && !b.ret.domain(), "memory access is defined");
  expect_unsat(inputs && !b.ret.val.non_poison, "loaded value is not poison");
  expect_unsat(inputs && b.ret.val.value != xv, "load returns the stored input");
}

} // namespace

int main() {
  smt::smt_initializer smt;
  util::config::disable_poison_input = true;
  util::config::disable_undef_input = true;

  IntType i32("i32", 32);
  IntType i1("i1", 1);
  PtrType ptr(0);

  arithmetic(i32);
  branch(i32, i1);
  memory(i32, ptr);

  if (g_failures != 0) {
    std::cerr << g_failures << " checks failed\n";
    return 1;
  }
  std::cout << "\nall direct-IR checks passed\n";
  return 0;
}
