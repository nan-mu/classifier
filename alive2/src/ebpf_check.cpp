#include "ebpf_check.h"

#include "smt/solver.h"
#include "smt/smt.h"

#include <cctype>
#include <filesystem>
#include <fstream>
#include <iostream>

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

void expect(bool cond, const std::string &name) {
  if (!cond) {
    std::cerr << "FAIL " << name << "\n";
    ++g_failures;
  } else {
    std::cout << "PASS " << name << "\n";
  }
}

static std::string save_model(const smt::Result &r, const std::string &name) {
  std::filesystem::create_directories("counterexamples");
  std::string path = "counterexamples/";
  for (char c : name)
    path += std::isalnum(static_cast<unsigned char>(c)) ? c : '_';
  path += ".smt2";
  std::ofstream out(path);
  out << r.getModel() << "\n";
  return path;
}

smt::Result check(const smt::expr &e, const std::string &name, bool want_unsat) {
  auto r = smt::check_expr(e, name.c_str(), true);
  bool ok = want_unsat ? r.isUnsat() : r.isSat();
  std::cout << (ok ? "PASS " : "FAIL ") << name << " " << answer_name(r) << "\n";
  if (r.isSat())
    std::cout << "counterexample " << save_model(r, name) << "\n";
  if (!ok) {
    ++g_failures;
    if (r.isSat())
      std::cout << r.getModel() << "\n";
    else if (!r.isUnsat())
      std::cout << "reason " << r.getReason() << "\n";
  }
  return r;
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
  smt::expr guard = input_ok(e);
  for (auto [reg, val] : env) {
    regs.r[reg] = val;
    for (const auto &[ireg, iname] : e.inputs) {
      if (ireg == reg)
        guard &= smt::expr::mkVar(iname.c_str(), 64) == smt::expr::mkUInt(val, 64);
    }
  }
  uint64_t concrete = interpret_ebpf(e.insns, regs);
  expect(concrete == want, name + " concrete reference");
  check(guard && !e.returned, name + " alive returns", true);
  check(guard && e.value != smt::expr::mkUInt(want, 64), name + " alive value",
        true);
}

void expect_sweep(const EbExec &e, const std::vector<std::vector<uint64_t>> &points,
                  const std::string &name) {
  auto ok = input_ok(e);
  smt::expr mismatch = false;
  for (const auto &point : points) {
    if (point.size() != e.inputs.size())
      throw std::runtime_error("sweep point width does not match the input count");
    ConcreteRegs regs;
    smt::expr guard = ok;
    for (size_t i = 0; i < e.inputs.size(); ++i) {
      regs.r[e.inputs[i].first] = point[i];
      guard &= smt::expr::mkVar(e.inputs[i].second.c_str(), 64) ==
               smt::expr::mkUInt(point[i], 64);
    }
    uint64_t want = interpret_ebpf(e.insns, regs);
    mismatch = mismatch ||
               (guard && (!e.returned || e.value != smt::expr::mkUInt(want, 64)));
  }
  check(mismatch, name + " sweep " + std::to_string(points.size()) + " points",
        true);
}

const std::vector<uint64_t> &boundary_values() {
  static const std::vector<uint64_t> v = {
      0, 1, 2, 0x7fffffff, 0x80000000, 0xffffffff, 0x100000000, 0x1ffffffff,
      0x7fffffffffffffff, 0x8000000000000000, 0xffffffffffffffff,
      0xdeadbeefcafebabe};
  return v;
}

std::vector<std::vector<uint64_t>> boundary_points(const EbExec &e) {
  const size_t n = e.inputs.size();
  std::vector<std::vector<uint64_t>> points;
  if (n == 0) {
    points.push_back({});
  } else if (n == 1) {
    for (uint64_t a : boundary_values())
      points.push_back({a});
  } else if (n == 2) {
    for (uint64_t a : boundary_values())
      for (uint64_t b : boundary_values())
        points.push_back({a, b});
  } else {
    // A full cross product is 12^n. Sweep one axis at a time plus the diagonal,
    // and keep every point exactly n wide.
    for (size_t axis = 0; axis < n; ++axis) {
      for (uint64_t v : boundary_values()) {
        std::vector<uint64_t> p(n, 0);
        p[axis] = v;
        points.push_back(std::move(p));
      }
    }
    for (uint64_t v : boundary_values())
      points.push_back(std::vector<uint64_t>(n, v));
  }
  return points;
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