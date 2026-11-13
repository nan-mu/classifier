#pragma once

#include <cstdint>
#include <stdexcept>
#include <string>
#include <variant>
#include <vector>

enum class EbWidth { W32, W64 };
enum class EbSrc { Reg, Imm };

struct EbAlu {
  EbWidth width;
  enum Op {
    Add, Sub, Mul, Div, Mod, Or, And, Lsh, Rsh, Neg, Xor, Mov, Arsh,
    Sdiv, Smod, Movsx
  } op;
  uint8_t dst;
  EbSrc src;
  uint8_t src_reg;
  int32_t imm;
  uint8_t offset = 0;
};

struct EbJmp {
  EbWidth width;
  enum Op {
    Ja, Jeq, Jne, Jgt, Jge, Jlt, Jle, Jsgt, Jsge, Jslt, Jsle, Exit
  } op;
  uint8_t dst;
  EbSrc src;
  uint8_t src_reg;
  int32_t imm;
  int32_t off;
  bool ja_uses_imm;
};

struct EbInsn {
  uint32_t index;
  std::variant<EbAlu, EbJmp> op;
};

enum class LiftBug {
  None,
  AddAsSub,
  Alu32AsAlu64,
  DivZeroAsUb,
  JumpPlusOne,
  SdivOverflowAsUb,
  ShiftWithoutMask,
  MovsxAsZext,
  ImmNoSignExtend
};

std::vector<EbInsn> decode_ebpf(const std::vector<uint8_t> &bytes);
std::string format_insn(const EbInsn &insn);
int jump_target(const EbInsn &insn);
