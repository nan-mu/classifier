#pragma once

#include "ebpf.h"
#include "ir/function.h"
#include "ir/type.h"

#include <string>
#include <utility>
#include <vector>

struct LiftInfo {
  std::string cfg;
  bool loop = false;
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
                   LiftBug bug);
