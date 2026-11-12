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

LiftInfo lift_ebpf(IR::Function &fn, IR::IntType &i64, IR::IntType &i32,
                   IR::IntType &i1, const std::vector<EbInsn> &code,
                   const std::vector<std::pair<uint8_t, std::string>> &inputs,
                   LiftBug bug);
