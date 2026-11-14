#pragma once

#include "ebpf.h"

#include <cstdint>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

enum class GateKind { Ready, Reject, IllFormed };

enum class SuccKind { Jump, Fall, Exit };

struct Succ {
  SuccKind kind = SuccKind::Fall;
  uint32_t pc = 0;
};

struct GateNode {
  uint32_t pc = 0;
  std::vector<Succ> succs;
};

struct Gate {
  GateKind kind = GateKind::Ready;
  uint32_t pc = 0;
  std::string reason;
  std::vector<GateNode> nodes;
};

class RegNum {
 public:
  static std::optional<RegNum> from_index(uint8_t index) {
    if (index > 9)
      return std::nullopt;
    return RegNum{index};
  }
  uint8_t index() const { return index_; }

 private:
  explicit RegNum(uint8_t index) : index_(index) {}
  uint8_t index_ = 0;
};

inline std::vector<RegNum> regs_from_inputs(
    const std::vector<std::pair<uint8_t, uint64_t>> &inputs) {
  std::vector<RegNum> out;
  out.reserve(inputs.size());
  for (auto [reg, bits] : inputs) {
    (void)bits;
    auto parsed = RegNum::from_index(reg);
    if (!parsed)
      throw std::invalid_argument("seed register");
    out.push_back(*parsed);
  }
  return out;
}

Gate gate(const std::vector<EbInsn> &insns, const std::vector<RegNum> &seeds);
