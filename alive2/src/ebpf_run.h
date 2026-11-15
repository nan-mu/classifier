#pragma once

#include "ebpf.h"
#include "ebpf_lift.h"
#include "smt/expr.h"

#include <array>
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

enum class CellTag { Input, Undef, Zero, Pointer, Bits };

struct AliveNode {
  std::string op;
  unsigned width = 0;
  std::vector<AliveNode> children;
  std::string constant;
  std::string var;
  bool partial = false;
};

struct AliveCell {
  CellTag tag = CellTag::Bits;
  bool undef = false;
  bool missing = false;
  AliveNode structure;
  smt::expr value;
  smt::expr non_poison;
  smt::expr domain;
};

struct AlivePhi {
  int reg = 0;
  std::string pred;
  AliveCell incoming;
  smt::expr pred_path;
};

inline AliveCell *alive_cell(std::array<AliveCell, 10> &cells, int reg) {
  if (reg < 0 || reg > 9)
    return nullptr;
  return &cells[reg];
}

inline const AliveCell *alive_cell(const std::array<AliveCell, 10> &cells, int reg) {
  if (reg < 0 || reg > 9)
    return nullptr;
  return &cells[reg];
}

struct AliveEdge {
  std::string block;
  int target_pc = -1;
  bool exit = false;
  AliveNode structure;
  smt::expr cond;
};

struct AlivePc {
  uint32_t pc = 0;
  std::string block;
  AliveNode path_structure;
  smt::expr path;
  std::array<AliveCell, 10> pre{};
  std::array<AliveCell, 10> post{};
  std::vector<AliveEdge> edges;
  std::vector<AlivePhi> phis;
  bool pointer_use = false;
};

struct AliveProgram {
  bool loop = false;
  std::string cfg;
  std::vector<AlivePc> pcs;
  std::vector<std::pair<uint8_t, std::string>> inputs;
};
