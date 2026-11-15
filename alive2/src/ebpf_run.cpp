#include "ebpf_run.h"

#include "ebpf_lift.h"
#include "ir/constant.h"
#include "ir/globals.h"
#include "ir/instr.h"
#include "ir/state.h"
#include "ir/value.h"
#include "smt/smt.h"
#include "util/config.h"
#include "util/symexec.h"

#include <sstream>

namespace {

void configure_pure_alu() {
  using namespace IR;
  num_locals_src = 0;
  num_locals_tgt = 0;
  num_nonlocals = 0;
  num_nonlocals_src = 0;
  num_globals_src = 0;
  num_ptrinputs = 0;
  has_fncall = false;
  has_alloca = false;
  has_null_block = false;
  has_int2ptr = false;
  has_nocapture = false;
  has_initializes_attr = false;
  does_int_load = false;
  does_int_store = false;
  does_ptr_load = false;
  does_ptr_store = false;
  observes_addresses = false;
}

} // namespace

EbExec execute_ebpf(const std::vector<uint8_t> &code,
                    std::vector<std::pair<uint8_t, std::string>> inputs,
                    unsigned unroll, LiftBug bug) {
  auto insns = decode_ebpf(code);
  std::ostringstream decoded;
  for (const auto &insn : insns)
    decoded << format_insn(insn);

  EbTypes types;
  IR::Function fn(types.i64, "ebpf");
  auto info = lift_ebpf(fn, types, insns, inputs, bug);
  if (info.loop) {
    if (unroll == 0)
      throw std::runtime_error("loop requires a non-zero Alive2 unroll bound");
    fn.unroll(unroll);
  } else {
    fn.topSort();
  }

  std::ostringstream ir;
  fn.print(ir);

  IR::State::resetGlobals();
  configure_pure_alu();
  util::config::disable_poison_input = true;
  util::config::disable_undef_input = true;
  IR::State state(fn, true);
  util::sym_exec(state);
  auto ret = state.returnVal();
  std::ostringstream memory;
  if (info.loop)
    memory << state.returnMemory();
  else
    memory << "none\n";

  EbExec out;
  out.decoded = decoded.str();
  out.cfg = info.cfg;
  out.ir = ir.str();
  out.memory = memory.str();
  out.value = ret.val.value;
  out.non_poison = ret.val.non_poison;
  out.defined = ret.domain();
  out.returned = ret.return_domain;
  out.insns = std::move(insns);
  out.inputs = std::move(inputs);
  return out;
}

namespace {

AliveNode walk_expr(const smt::expr &expr, int depth) {
  AliveNode node;
  if (!expr.isValid() || depth > 48) {
    node.op = "partial";
    node.partial = true;
    return node;
  }
  if (expr.isTrue()) {
    node.op = "const";
    node.constant = "1";
    node.width = 1;
    return node;
  }
  if (expr.isFalse()) {
    node.op = "const";
    node.constant = "0";
    node.width = 1;
    return node;
  }
  if (expr.isBV() && expr.isConst()) {
    node.op = "const";
    node.width = expr.bits();
    node.constant = std::string(expr.numeral_string());
    return node;
  }
  if (expr.isVar()) {
    node.op = "var";
    node.var = std::string(expr.fn_name());
    node.width = expr.isBV() ? expr.bits() : 1;
    return node;
  }
  smt::expr cond, left, right;
  if (expr.isIf(cond, left, right)) {
    node.op = "ite";
    if (expr.isBV())
      node.width = expr.bits();
    node.children = {walk_expr(cond, depth + 1), walk_expr(left, depth + 1),
                     walk_expr(right, depth + 1)};
  } else if (expr.isAdd(left, right)) {
    node.op = "add";
    node.width = expr.isBV() ? expr.bits() : 0;
    node.children = {walk_expr(left, depth + 1), walk_expr(right, depth + 1)};
  } else {
    auto name = std::string(expr.fn_name());
    if (name.empty()) {
      node.op = "partial";
      node.partial = true;
      return node;
    }
    node.op = std::move(name);
    if (expr.isBV())
      node.width = expr.bits();
    unsigned argc = expr.getFnNumArgs();
    if (argc > 8) {
      node.partial = true;
      return node;
    }
    for (unsigned i = 0; i < argc; ++i)
      node.children.push_back(walk_expr(expr.getFnArg(i), depth + 1));
  }
  for (const auto &child : node.children) {
    if (child.partial)
      node.partial = true;
  }
  return node;
}

CellTag tag_of(const EbSlot &slot) {
  if (slot.origin == RegOrigin::Pointer)
    return CellTag::Pointer;
  if (slot.origin == RegOrigin::Undef)
    return CellTag::Undef;
  if (slot.origin == RegOrigin::Input)
    return CellTag::Input;
  if (auto *constant = dynamic_cast<IR::IntConst *>(slot.value)) {
    if (auto *bits = constant->getInt(); bits && *bits == 0)
      return CellTag::Zero;
  }
  if (slot.origin == RegOrigin::Zero)
    return CellTag::Zero;
  return CellTag::Bits;
}

AliveCell cell_from(IR::State &state, const EbSlot &slot, bool allow_exec) {
  AliveCell cell;
  cell.tag = tag_of(slot);
  if (!slot.value || cell.tag == CellTag::Pointer) {
    cell.missing = cell.tag != CellTag::Pointer;
    return cell;
  }
  const IR::State::ValTy *got = state.at(*slot.value);
  if (!got && allow_exec && cell.tag == CellTag::Undef) {
    state.exec(*slot.value);
    got = state.at(*slot.value);
  }
  if (!got) {
    cell.missing = true;
    return cell;
  }
  cell.value = got->val.value;
  cell.non_poison = got->val.non_poison;
  cell.undef = cell.tag == CellTag::Undef || got->undef_vars.count(cell.value) != 0;
  cell.structure = walk_expr(cell.value, 0);
  return cell;
}

EbSlot slot_for(IR::Value *value) {
  EbSlot slot;
  slot.value = value;
  slot.origin = RegOrigin::Value;
  if (dynamic_cast<IR::PoisonValue *>(value))
    slot.origin = RegOrigin::Pointer;
  else if (dynamic_cast<IR::UndefValue *>(value))
    slot.origin = RegOrigin::Undef;
  else if (dynamic_cast<IR::Input *>(value))
    slot.origin = RegOrigin::Input;
  return slot;
}

} // namespace

AliveProgram observe_ebpf(const std::vector<uint8_t> &code,
                          std::vector<std::pair<uint8_t, std::string>> inputs,
                          LiftBug bug) {
  auto insns = decode_ebpf(code);
  EbTypes types;
  IR::Function fn(types.i64, "ebpf");
  auto info = lift_ebpf(fn, types, insns, inputs, bug, LiftInit::Rocq);
  AliveProgram program;
  program.loop = info.loop;
  program.cfg = info.cfg;
  program.inputs = inputs;
  if (info.loop)
    return program;

  fn.topSort();
  IR::State::resetGlobals();
  configure_pure_alu();
  util::config::disable_poison_input = true;
  util::config::disable_undef_input = true;
  IR::State state(fn, true);
  util::sym_exec(state);

  program.pcs.reserve(info.sites.size());
  for (const auto &site : info.sites) {
    AlivePc pc;
    pc.pc = site.pc;
    pc.block = site.block_name;
    pc.pointer_use = site.pointer_use;
    if (site.block) {
      pc.path = state.getPath(*site.block);
      pc.path_structure = walk_expr(pc.path, 0);
    }
    for (const auto &edge : site.edges) {
      AliveEdge out;
      out.block = edge.name;
      out.target_pc = edge.target_pc;
      out.exit = edge.exit;
      if (edge.exit)
        out.cond = pc.path;
      else if (site.term && edge.block)
        out.cond = state.getJumpCond(*site.term, *edge.block);
      out.structure = walk_expr(out.cond, 0);
      pc.edges.push_back(std::move(out));
    }
    for (int reg = 0; reg < 10; ++reg) {
      pc.pre[reg] = cell_from(state, site.pre[reg], false);
      pc.post[reg] = cell_from(state, site.post[reg], false);
      if (auto *phi = dynamic_cast<IR::Phi *>(site.post[reg].value)) {
        for (const auto &incoming : phi->getValues()) {
          AlivePhi arm;
          arm.reg = reg;
          arm.pred = incoming.second;
          arm.incoming = cell_from(state, slot_for(incoming.first), false);
          pc.phis.push_back(std::move(arm));
        }
      }
    }
    program.pcs.push_back(std::move(pc));
  }
  for (size_t i = 0; i < program.pcs.size(); ++i) {
    auto &pc = program.pcs[i];
    for (int reg = 0; reg < 10; ++reg) {
      if (pc.pre[reg].missing && pc.pre[reg].tag == CellTag::Undef)
        pc.pre[reg] = cell_from(state, info.sites[i].pre[reg], true);
      if (pc.post[reg].missing && pc.post[reg].tag == CellTag::Undef)
        pc.post[reg] = cell_from(state, info.sites[i].post[reg], true);
    }
  }
  return program;
}
