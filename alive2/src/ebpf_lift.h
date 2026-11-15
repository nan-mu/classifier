#pragma once

#include "ebpf.h"
#include "ir/function.h"
#include "ir/type.h"

#include <array>
#include <string>
#include <utility>
#include <vector>

// Zero is the historical constant init. Rocq is the symbolic caller only.
enum class LiftInit { Zero, Rocq };

enum class RegOrigin { Zero, Input, Undef, Pointer, Value };

struct EbSlot {
  IR::Value *value = nullptr;
  RegOrigin origin = RegOrigin::Zero;
};

struct EbEdge {
  IR::BasicBlock *block = nullptr;
  std::string name;
  int target_pc = -1;
  bool exit = false;
};

// One eBPF instruction. Value pointers belong to the Function, not the Lifter.
struct EbSite {
  uint32_t pc = 0;
  IR::BasicBlock *block = nullptr;
  std::string block_name;
  IR::BasicBlock *term = nullptr;
  std::array<EbSlot, 10> pre{};
  std::array<EbSlot, 10> post{};
  std::vector<EbEdge> edges;
  bool pointer_use = false;
};

struct LiftInfo {
  std::string cfg;
  bool loop = false;
  std::vector<EbSite> sites;
};

// The IR keeps Type references, so these must outlive the Function, not the
// Lifter that fills it.
struct EbTypes {
  IR::IntType i64{"i64", 64};
  IR::IntType i32{"i32", 32};
  IR::IntType i1{"i1", 1};
  IR::IntType i8{"i8", 8};
  IR::IntType i16{"i16", 16};
};

LiftInfo lift_ebpf(IR::Function &fn, EbTypes &types,
                   const std::vector<EbInsn> &code,
                   const std::vector<std::pair<uint8_t, std::string>> &inputs,
                   LiftBug bug, LiftInit init = LiftInit::Zero);
