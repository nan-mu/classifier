#include "ebpf_run.h"

#include "ebpf_lift.h"
#include "ir/globals.h"
#include "ir/state.h"
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

  IR::IntType i64("i64", 64);
  IR::IntType i32("i32", 32);
  IR::IntType i1("i1", 1);
  IR::Function fn(i64, "ebpf");
  auto info = lift_ebpf(fn, i64, i32, i1, insns, inputs, bug);
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
