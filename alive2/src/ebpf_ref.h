#pragma once

#include "ebpf.h"
#include "smt/expr.h"

#include <array>
#include <cstdint>

struct ConcreteRegs {
  uint64_t r[11]{};
};

uint64_t interpret_ebpf(const std::vector<EbInsn> &code, ConcreteRegs regs,
                        uint32_t step_cap = 100000);

struct SymRef {
  smt::expr r0;
  smt::expr returns;
};

SymRef interpret_ebpf_sym(const std::vector<EbInsn> &code,
                          const std::array<smt::expr, 11> &regs,
                          unsigned backedge_fuel);
