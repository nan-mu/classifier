#pragma once

#include "ebpf.h"
#include "smt/expr.h"

#include <string>
#include <utility>
#include <vector>

struct EbExec {
  std::string decoded;
  std::string cfg;
  std::string ir;
  std::string memory;
  smt::expr value;
  smt::expr non_poison;
  smt::expr defined;
  smt::expr returned;
  std::vector<EbInsn> insns;
  std::vector<std::pair<uint8_t, std::string>> inputs;
};

EbExec execute_ebpf(const std::vector<uint8_t> &code,
                    std::vector<std::pair<uint8_t, std::string>> inputs,
                    unsigned unroll, LiftBug bug = LiftBug::None);
