#pragma once

#include "ebpf_ref.h"
#include "ebpf_run.h"
#include "smt/expr.h"
#include "smt/solver.h"

#include <array>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

extern int g_failures;

const char *answer_name(const smt::Result &r);
void expect(bool cond, const std::string &name);
smt::Result check(const smt::expr &e, const std::string &name, bool want_unsat);

smt::expr input_ok(const EbExec &e);
std::array<smt::expr, 11> sym_regs(const EbExec &e);
void expect_equiv(const EbExec &e, const std::string &name);
void expect_at(const EbExec &e, const std::vector<std::pair<uint8_t, uint64_t>> &env,
               uint64_t want, const std::string &name);
void expect_sweep(const EbExec &e, const std::vector<std::vector<uint64_t>> &points,
                  const std::string &name);
const std::vector<uint64_t> &boundary_values();
std::vector<std::vector<uint64_t>> boundary_points(const EbExec &e);
void print_sample(const EbExec &e);