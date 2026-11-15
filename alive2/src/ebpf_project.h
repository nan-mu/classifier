#pragma once

#include "ebpf.h"
#include "ebpf_run.h"

#include <string>
#include <vector>

enum class Verdict { Equivalent, Counterexample, Unknown, Unsupported };

struct RNode {
  enum class Kind {
    Const, Var, Undef, Pointer, Add, Sub, Udiv, Eq, Ugt, Not, And, Or, Ite,
    True, False
  } kind = Kind::False;
  CellTag tag = CellTag::Bits;
  uint64_t imm = 0;
  std::string var;
  std::string cite;
  std::string note;
  std::vector<RNode> kids;
};

struct CheckedCell {
  CellTag alive_tag = CellTag::Bits;
  CellTag rocq_tag = CellTag::Bits;
  Verdict definedness = Verdict::Unsupported;
  Verdict value = Verdict::Unsupported;
  std::string model;
  std::string smt;
  AliveNode alive;
  RNode rocq;
};

struct CheckedPhi {
  int reg = 0;
  std::string pred;
  Verdict verdict = Verdict::Unsupported;
  std::string model;
  std::string smt;
  AliveNode alive;
  RNode rocq;
};

struct CheckedEdge {
  std::string block;
  int target_pc = -1;
  bool exit = false;
  Verdict verdict = Verdict::Unsupported;
  std::string model;
  std::string smt;
  AliveNode alive;
  RNode rocq;
};

struct CheckedPc {
  uint32_t pc = 0;
  std::string insn;
  std::string block;
  std::vector<std::string> rules;
  Verdict path = Verdict::Unsupported;
  std::string path_model;
  std::string path_smt;
  AliveNode alive_path;
  RNode rocq_path;
  std::vector<CheckedCell> pre;
  std::vector<CheckedCell> post;
  std::vector<CheckedEdge> edges;
  std::vector<CheckedPhi> phis;
  std::string reason;
};

struct CrossObs {
  int reg = 0;
  std::string projection;
  std::string rocq;
  std::string verdict;
};

struct CrossStep {
  uint32_t pc = 0;
  std::string status;
  std::string successor;
  std::string rocq_status;
  std::string rocq_successor;
  std::string ret_projection;
  std::string ret_rocq;
  std::string ret_verdict;
  bool match = false;
  std::string error;
  std::vector<CrossObs> pre;
  std::vector<CrossObs> post;
};

struct CrossCheck {
  std::string label;
  std::string projection;
  std::string rocq;
  bool match = false;
  std::string error;
  std::vector<CrossStep> steps;
};

struct CheckedProgram {
  std::string label;
  std::string bytes;
  std::string bug;
  std::string gate = "ready";
  uint32_t gate_pc = 0;
  std::string gate_reason;
  bool loop = false;
  std::vector<std::string> assumptions;
  std::string assumption_smt;
  bool phi_swap_rejected = false;
  bool phi_drop_unsupported = false;
  std::vector<CheckedPc> pcs;
  std::vector<CrossCheck> cross;
};

struct ConcreteStepOut {
  uint32_t pc = 0;
  std::string status;
  std::string pc_after;
  std::string r0;
};

struct ConcreteRow {
  std::string id;
  bool agree = false;
  std::string divergence;
  std::vector<ConcreteStepOut> steps;
};

struct ExhibitDoc {
  std::string projection;
  std::vector<CheckedProgram> programs;
  std::vector<ConcreteRow> concrete;
};

ExhibitDoc analyze_default();
CheckedProgram analyze_bytes(const std::vector<uint8_t> &code,
                             std::vector<std::pair<uint8_t, std::string>> inputs,
                             std::vector<std::pair<uint8_t, uint64_t>> concrete,
                             LiftBug bug, const std::string &label);

const char *exhibit_projection();

std::string exhibit_json(const ExhibitDoc &doc);

// Prints the contract's four lines. Returns 0 when they hold.
int symbolic_check();
