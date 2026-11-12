#include "ebpf.h"

#include <sstream>

namespace {

constexpr uint8_t kClass = 0x07;
constexpr uint8_t kSrc = 0x08;
constexpr uint8_t kOp = 0xf0;
constexpr uint8_t kAlu = 0x04;
constexpr uint8_t kJmp = 0x05;
constexpr uint8_t kJmp32 = 0x06;
constexpr uint8_t kAlu64 = 0x07;

[[noreturn]] void bad(uint32_t index, const std::string &why) {
  throw std::runtime_error("eBPF insn " + std::to_string(index) + ": " + why);
}

void check_reg(uint32_t index, unsigned reg, const char *what) {
  if (reg > 10)
    bad(index, std::string(what) + " r" + std::to_string(reg) + " is out of range");
}

} // namespace

int jump_target(const EbInsn &insn) {
  const auto &j = std::get<EbJmp>(insn.op);
  if (j.op == EbJmp::Exit)
    return -1;
  int32_t disp = j.ja_uses_imm ? j.imm : j.off;
  return static_cast<int>(insn.index) + 1 + disp;
}

std::vector<EbInsn> decode_ebpf(const std::vector<uint8_t> &bytes) {
  if (bytes.size() % 8 != 0)
    throw std::runtime_error("eBPF bytecode length is not a multiple of 8");
  std::vector<EbInsn> out;
  out.reserve(bytes.size() / 8);
  for (size_t off = 0; off < bytes.size(); off += 8) {
    uint32_t index = static_cast<uint32_t>(off / 8);
    uint8_t opcode = bytes[off];
    uint8_t regs = bytes[off + 1];
    uint8_t dst = regs & 0x0f;
    uint8_t src = regs >> 4;
    int16_t disp = static_cast<int16_t>(bytes[off + 2] |
                                        (static_cast<uint16_t>(bytes[off + 3]) << 8));
    int32_t imm = static_cast<int32_t>(
        static_cast<uint32_t>(bytes[off + 4]) |
        (static_cast<uint32_t>(bytes[off + 5]) << 8) |
        (static_cast<uint32_t>(bytes[off + 6]) << 16) |
        (static_cast<uint32_t>(bytes[off + 7]) << 24));
    check_reg(index, dst, "dst");
    check_reg(index, src, "src");

    uint8_t cls = opcode & kClass;
    uint8_t code = opcode & kOp;
    bool reg_src = opcode & kSrc;
    EbInsn insn;
    insn.index = index;

    if (cls == kAlu || cls == kAlu64) {
      EbAlu alu;
      alu.width = cls == kAlu64 ? EbWidth::W64 : EbWidth::W32;
      alu.dst = dst;
      alu.src = reg_src ? EbSrc::Reg : EbSrc::Imm;
      alu.src_reg = src;
      alu.imm = imm;
      if (code == 0x80) {
        if (reg_src)
          bad(index, "NEG with register source is not in the ISA");
        alu.op = EbAlu::Neg;
      } else if (code == 0x30 || code == 0x90) {
        if (disp == 1)
          bad(index, "signed DIV/MOD is outside this PoC");
        if (disp != 0)
          bad(index, "ALU offset must be 0 for unsigned DIV/MOD");
        alu.op = code == 0x30 ? EbAlu::Div : EbAlu::Mod;
      } else if (code == 0xb0) {
        if (disp != 0)
          bad(index, "MOVSX is outside this PoC");
        alu.op = EbAlu::Mov;
      } else if (disp != 0) {
        bad(index, "non-zero ALU offset is not a supported instruction");
      } else {
        switch (code) {
        case 0x00: alu.op = EbAlu::Add; break;
        case 0x10: alu.op = EbAlu::Sub; break;
        case 0x20: alu.op = EbAlu::Mul; break;
        case 0x40: alu.op = EbAlu::Or; break;
        case 0x50: alu.op = EbAlu::And; break;
        case 0x60: alu.op = EbAlu::Lsh; break;
        case 0x70: alu.op = EbAlu::Rsh; break;
        case 0xa0: alu.op = EbAlu::Xor; break;
        case 0xc0: alu.op = EbAlu::Arsh; break;
        default:
          bad(index, "unsupported ALU opcode 0x" +
                         ([&] {
                           std::ostringstream os;
                           os << std::hex << int(opcode);
                           return os.str();
                         })());
        }
      }
      if (alu.src == EbSrc::Imm && src != 0 && alu.op != EbAlu::Neg)
        bad(index, "immediate ALU source register must be zero");
      insn.op = alu;
    } else if (cls == kJmp || cls == kJmp32) {
      EbJmp jmp;
      jmp.width = cls == kJmp32 ? EbWidth::W32 : EbWidth::W64;
      jmp.dst = dst;
      jmp.src = reg_src ? EbSrc::Reg : EbSrc::Imm;
      jmp.src_reg = src;
      jmp.imm = imm;
      jmp.off = disp;
      jmp.ja_uses_imm = false;
      if (code == 0x90) {
        if (cls != kJmp || reg_src || disp != 0 || src != 0 || dst != 0)
          bad(index, "malformed EXIT");
        jmp.op = EbJmp::Exit;
      } else if (code == 0x00) {
        if (reg_src || src != 0 || dst != 0)
          bad(index, "malformed JA");
        jmp.op = EbJmp::Ja;
        if (cls == kJmp32) {
          jmp.ja_uses_imm = true;
          if (disp != 0)
            bad(index, "JMP32 JA offset field must be zero");
        } else if (imm != 0) {
          bad(index, "JMP JA immediate must be zero");
        }
      } else {
        switch (code) {
        case 0x10: jmp.op = EbJmp::Jeq; break;
        case 0x50: jmp.op = EbJmp::Jne; break;
        case 0x20: jmp.op = EbJmp::Jgt; break;
        case 0x30: jmp.op = EbJmp::Jge; break;
        case 0xa0: jmp.op = EbJmp::Jlt; break;
        case 0xb0: jmp.op = EbJmp::Jle; break;
        case 0x60: jmp.op = EbJmp::Jsgt; break;
        case 0x70: jmp.op = EbJmp::Jsge; break;
        case 0xc0: jmp.op = EbJmp::Jslt; break;
        case 0xd0: jmp.op = EbJmp::Jsle; break;
        default:
          bad(index, "unsupported jump opcode");
        }
        if (jmp.src == EbSrc::Imm && src != 0)
          bad(index, "immediate jump source register must be zero");
      }
      insn.op = jmp;
    } else {
      std::ostringstream os;
      os << "unsupported class in opcode 0x" << std::hex << int(opcode);
      bad(index, os.str());
    }
    out.push_back(insn);
  }
  return out;
}

std::string format_insn(const EbInsn &insn) {
  std::ostringstream os;
  os << insn.index << ": ";
  if (const auto *alu = std::get_if<EbAlu>(&insn.op)) {
    const char *name = "?";
    switch (alu->op) {
    case EbAlu::Add: name = "add"; break;
    case EbAlu::Sub: name = "sub"; break;
    case EbAlu::Mul: name = "mul"; break;
    case EbAlu::Div: name = "div"; break;
    case EbAlu::Mod: name = "mod"; break;
    case EbAlu::Or: name = "or"; break;
    case EbAlu::And: name = "and"; break;
    case EbAlu::Lsh: name = "lsh"; break;
    case EbAlu::Rsh: name = "rsh"; break;
    case EbAlu::Neg: name = "neg"; break;
    case EbAlu::Xor: name = "xor"; break;
    case EbAlu::Mov: name = "mov"; break;
    case EbAlu::Arsh: name = "arsh"; break;
    }
    os << (alu->width == EbWidth::W64 ? "alu64 " : "alu32 ") << name << " r"
       << int(alu->dst);
    if (alu->op != EbAlu::Neg) {
      if (alu->src == EbSrc::Reg)
        os << ", r" << int(alu->src_reg);
      else
        os << ", " << alu->imm;
    }
  } else {
    const auto &jmp = std::get<EbJmp>(insn.op);
    const char *name = "?";
    switch (jmp.op) {
    case EbJmp::Ja: name = "ja"; break;
    case EbJmp::Jeq: name = "jeq"; break;
    case EbJmp::Jne: name = "jne"; break;
    case EbJmp::Jgt: name = "jgt"; break;
    case EbJmp::Jge: name = "jge"; break;
    case EbJmp::Jlt: name = "jlt"; break;
    case EbJmp::Jle: name = "jle"; break;
    case EbJmp::Jsgt: name = "jsgt"; break;
    case EbJmp::Jsge: name = "jsge"; break;
    case EbJmp::Jslt: name = "jslt"; break;
    case EbJmp::Jsle: name = "jsle"; break;
    case EbJmp::Exit: name = "exit"; break;
    }
    os << (jmp.width == EbWidth::W32 ? "jmp32 " : "jmp ") << name;
    if (jmp.op == EbJmp::Exit) {
      os << "\n";
      return os.str();
    }
    if (jmp.op != EbJmp::Ja) {
      os << " r" << int(jmp.dst) << ", ";
      if (jmp.src == EbSrc::Reg)
        os << "r" << int(jmp.src_reg);
      else
        os << jmp.imm;
      os << ", ";
    }
    if (jmp.op == EbJmp::Ja)
      os << ' ';
    os << (jmp.ja_uses_imm ? jmp.imm : jmp.off);
  }
  os << "\n";
  return os.str();
}
