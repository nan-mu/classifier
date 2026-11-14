#include "ebpf.h"
#include "ebpf_concrete.h"
#include "ebpf_gate.h"
#include "ebpf_run.h"
#include "smt/smt.h"

#include <cctype>
#include <cstdio>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace {

std::vector<uint8_t> parse_hex(std::string_view hex) {
  if (hex.size() % 2 != 0)
    throw std::runtime_error("odd hex length");
  std::vector<uint8_t> out;
  out.reserve(hex.size() / 2);
  auto nyb = [](char c) -> int {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
  };
  for (size_t i = 0; i < hex.size(); i += 2) {
    int hi = nyb(hex[i]);
    int lo = nyb(hex[i + 1]);
    if (hi < 0 || lo < 0)
      throw std::runtime_error("bad hex");
    out.push_back(static_cast<uint8_t>((hi << 4) | lo));
  }
  return out;
}

std::string hex16(uint64_t bits) {
  char buf[17];
  std::snprintf(buf, sizeof buf, "%016llx",
                static_cast<unsigned long long>(bits));
  return buf;
}

const char *status_name(StepStatus status) {
  switch (status) {
  case StepStatus::Next: return "NEXT";
  case StepStatus::Exit: return "EXIT";
  case StepStatus::Stuck: return "STUCK";
  case StepStatus::Ub: return "UB";
  case StepStatus::Incomplete: return "INCOMPLETE";
  case StepStatus::Unsupported: return "UNSUPPORTED";
  }
  return "UNSUPPORTED";
}

std::string pc_text(const PcAfter &pc) {
  if (auto *idx = std::get_if<InsnPc>(&pc))
    return "pc" + std::to_string(idx->index);
  if (std::holds_alternative<ExitPc>(pc))
    return "exit";
  return "none";
}

std::string obs_text(const Obs &obs) {
  if (std::holds_alternative<std::monostate>(obs))
    return "UNDEF";
  if (auto *bits = std::get_if<Bv64>(&obs))
    return hex16(bits->bits);
  const auto &ptr = std::get<Ptr>(obs);
  const char *role = "other";
  switch (ptr.role) {
  case PtrRole::Code: role = "code"; break;
  case PtrRole::Stack: role = "stack"; break;
  case PtrRole::Ctx: role = "ctx"; break;
  case PtrRole::Other: role = "other"; break;
  }
  return std::string("PTR ") + role + " " + hex16(ptr.offset);
}

std::string regs_text(const RegFile &regs) {
  std::string out;
  for (int i = 0; i < 10; ++i) {
    if (i)
      out += " ";
    out += "r" + std::to_string(i) + "=" + obs_text(regs.r[i]);
  }
  return out;
}

std::string undef_sentence(const RegFile &after) {
  std::vector<int> regs;
  for (int i = 0; i < 10; ++i) {
    if (std::holds_alternative<std::monostate>(after.r[i]))
      regs.push_back(i);
  }
  if (regs.empty())
    return "";
  std::string list;
  for (size_t i = 0; i < regs.size(); ++i) {
    if (i == 0)
      list += "r" + std::to_string(regs[i]);
    else if (i + 1 == regs.size())
      list += (regs.size() == 2 ? " and r" : ", and r") + std::to_string(regs[i]);
    else
      list += ", r" + std::to_string(regs[i]);
  }
  if (regs.size() == 1)
    return list + " is UNDEF on the Rocq side. The comparator skips that cell "
                  "because that register was not read.";
  return list + " are UNDEF on the Rocq side. The comparator skips those cells "
                "because those registers were not read.";
}

const Fixture &need_fixture(const char *id) {
  for (const auto &fixture : kFixtures()) {
    if (std::string(fixture.id) == id)
      return fixture;
  }
  throw std::runtime_error(std::string("missing fixture ") + id);
}

const Step *find_step(const Trace &trace, uint32_t pc) {
  for (const auto &step : trace.steps) {
    if (step.pc.index == pc)
      return &step;
  }
  return nullptr;
}

bool takes(const Step &step, const Succ &succ) {
  if (succ.kind == SuccKind::Exit)
    return std::holds_alternative<ExitPc>(step.pc_after);
  if (auto *idx = std::get_if<InsnPc>(&step.pc_after))
    return idx->index == succ.pc;
  return false;
}

bool has_id(const std::string &text, const std::string &id) {
  size_t pos = 0;
  while ((pos = text.find(id, pos)) != std::string::npos) {
    size_t end = pos + id.size();
    if (end == text.size() || !std::isdigit(static_cast<unsigned char>(text[end])))
      return true;
    pos = end;
  }
  return false;
}

bool defines_name(const std::filesystem::path &path, const std::string &name) {
  std::ifstream in(path);
  if (!in)
    return false;
  std::string text((std::istreambuf_iterator<char>(in)), {});
  std::string live;
  int nest = 0;
  for (size_t i = 0; i < text.size(); ++i) {
    if (i + 1 < text.size() && text[i] == '(' && text[i + 1] == '*') {
      ++nest;
      ++i;
      continue;
    }
    if (nest && i + 1 < text.size() && text[i] == '*' && text[i + 1] == ')') {
      --nest;
      ++i;
      continue;
    }
    if (nest == 0)
      live.push_back(text[i]);
  }
  const std::string needle = "Definition " + name;
  size_t pos = 0;
  while ((pos = live.find(needle, pos)) != std::string::npos) {
    bool at_line = pos == 0 || live[pos - 1] == '\n';
    size_t end = pos + needle.size();
    char after = end < live.size() ? live[end] : ' ';
    bool boundary = !(std::isalnum(static_cast<unsigned char>(after)) || after == '_');
    if (at_line && boundary)
      return true;
    pos = end;
  }
  return false;
}

std::vector<const char *> cite_names(const EbInsn &insn) {
  std::vector<const char *> names{"exec_instr"};
  if (const auto *alu = std::get_if<EbAlu>(&insn.op)) {
    if (alu->width != EbWidth::W64)
      throw std::runtime_error("exhibit cites alu64 only");
    names.push_back("exec_alu");
    names.push_back("eval_alu64");
    if (alu->op == EbAlu::Div)
      names.push_back("eval_div_u64");
    else if (alu->op != EbAlu::Mov && alu->op != EbAlu::Add &&
             alu->op != EbAlu::Sub)
      throw std::runtime_error("exhibit has no citation for this alu");
    names.push_back("nextinstr");
    return names;
  }
  const auto &jmp = std::get<EbJmp>(insn.op);
  if (jmp.op == EbJmp::Exit) {
    names.push_back("exec_ret");
    return names;
  }
  if (jmp.width != EbWidth::W64)
    throw std::runtime_error("exhibit cites jmp64 only");
  if (jmp.op == EbJmp::Ja) {
    names.push_back("exec_jmp64");
    names.push_back("nextinstr");
    return names;
  }
  if (jmp.op == EbJmp::Jgt) {
    names.push_back("exec_jmpcmp");
    names.push_back("eval_cmp_static");
    names.push_back("eval_cmp64");
    names.push_back("nextinstr");
    return names;
  }
  throw std::runtime_error("exhibit has no citation for this jump");
}

const char *next_def(const EbInsn &insn) {
  if (std::holds_alternative<EbAlu>(insn.op))
    return "exec_alu";
  const auto &jmp = std::get<EbJmp>(insn.op);
  if (jmp.op == EbJmp::Exit)
    return "exec_ret";
  if (jmp.op == EbJmp::Ja)
    return "exec_jmp64";
  return "exec_jmpcmp";
}

std::string ret_text(const std::optional<Bv64> &value) {
  return value ? hex16(value->bits) : std::string("none");
}

struct Pair {
  const Trace *rocq;
  const Trace *alive;
};

struct Parts {
  std::string graph;
  std::string cites;
  std::string steps;
};

const EbInsn &insn_at(const std::vector<EbInsn> &insns, uint32_t pc) {
  for (const auto &candidate : insns) {
    if (candidate.index == pc)
      return candidate;
  }
  throw std::runtime_error("gate node has no instruction");
}

std::string one_line(const EbInsn &insn) {
  std::string text = format_insn(insn);
  while (!text.empty() && (text.back() == '\n' || text.back() == '\r'))
    text.pop_back();
  auto pos = text.find(": ");
  if (pos != std::string::npos)
    text = text.substr(pos + 2);
  return text;
}

std::string transition_condition(const EbInsn &insn, SuccKind kind) {
  if (kind == SuccKind::Exit)
    return "exit";
  if (const auto *jmp = std::get_if<EbJmp>(&insn.op)) {
    if (jmp->op == EbJmp::Ja)
      return "ja";
    std::string body = one_line(insn);
    if (kind == SuccKind::Fall)
      return "not " + body;
    return body;
  }
  return one_line(insn);
}

std::string reg_delta(const RegFile &before, const RegFile &after) {
  std::string out;
  for (int i = 0; i < 10; ++i) {
    std::string from = obs_text(before.r[i]);
    std::string to = obs_text(after.r[i]);
    if (from == to)
      continue;
    if (!out.empty())
      out += ", ";
    out += "r" + std::to_string(i) + " " + from + " to " + to;
  }
  return out;
}

std::string step_cell(const Step *step) {
  if (!step)
    return "not recorded";
  std::string cell =
      std::string(status_name(step->status)) + " to " + pc_text(step->pc_after);
  std::string changed = reg_delta(step->before, step->after);
  if (!changed.empty())
    cell += ", " + changed;
  return cell;
}

void append_insn_table(std::ostringstream &md, const Gate &program,
                       const std::vector<EbInsn> &insns,
                       const std::vector<Pair> &inputs,
                       const std::string &structural, const std::string &ub_id,
                       const std::string &ub_line) {
  md << "| pc | instruction | input | Rocq | Alive2 | Concrete PASS | "
        "Structural Match | Not Established |\n";
  md << "| --- | --- | --- | --- | --- | --- | --- | --- |\n";
  const char *not_est =
      "This input is not all inputs. See Missing from the Alive2 step.";
  for (const auto &node : program.nodes) {
    std::string insn = one_line(insn_at(insns, node.pc));
    for (const auto &input : inputs) {
      const Step *rocq = find_step(*input.rocq, node.pc);
      const Step *alive = find_step(*input.alive, node.pc);
      if (!rocq && !alive)
        continue;
      std::string pass = "Yes. This input's traces agree.";
      if (input.rocq->case_id == ub_id) {
        if (alive && alive->status == StepStatus::Ub)
          pass = "No. " + ub_line;
        else
          pass = "No. This input diverges at pc 1.";
      }
      md << "| " << node.pc << " | " << insn << " | " << input.rocq->case_id
         << " | " << step_cell(rocq) << " | " << step_cell(alive) << " | "
         << pass << " | " << structural << " | " << not_est << " |\n";
    }
  }
  md << "\n";
}

Parts build_parts(const Gate &program, const std::vector<EbInsn> &insns,
                  const std::vector<Pair> &inputs,
                  const std::vector<const Trace *> &edge_marks,
                  const std::vector<std::string> &stops) {
  for (const Trace *mark : edge_marks) {
    for (const auto &step : mark->steps) {
      if (std::holds_alternative<std::monostate>(step.pc_after))
        continue;
      const GateNode *node = nullptr;
      for (const auto &candidate : program.nodes) {
        if (candidate.pc == step.pc.index)
          node = &candidate;
      }
      bool matched = false;
      if (node) {
        for (const auto &succ : node->succs) {
          if (takes(step, succ))
            matched = true;
        }
      }
      if (!matched)
        throw std::runtime_error("trace edge is not in the gate at pc " +
                                 std::to_string(step.pc.index));
    }
  }

  Parts parts;
  std::ostringstream graph;
  graph << "```mermaid\nflowchart TD\n";
  for (const auto &node : program.nodes) {
    const EbInsn &insn = insn_at(insns, node.pc);
    graph << "  pc" << node.pc << "[\"pc " << node.pc << " " << one_line(insn)
          << "\"]\n";
  }
  graph << "  exit[\"exit\"]\n";
  for (const auto &node : program.nodes) {
    const EbInsn &insn = insn_at(insns, node.pc);
    for (const auto &succ : node.succs) {
      std::string label = transition_condition(insn, succ.kind);
      for (const Trace *mark : edge_marks) {
        const Step *step = find_step(*mark, node.pc);
        if (!step || !takes(*step, succ))
          continue;
        label += std::string(" ") + mark->case_id;
        const Trace *alive = nullptr;
        for (const auto &input : inputs) {
          if (input.rocq->case_id == mark->case_id)
            alive = input.alive;
        }
        if (alive) {
          const Step *alive_step = find_step(*alive, node.pc);
          if (alive_step && takes(*alive_step, succ)) {
            std::string changed = reg_delta(alive_step->before, alive_step->after);
            if (!changed.empty())
              label += " " + changed;
          }
        }
      }
      graph << "  pc" << node.pc << " -->|\"" << label << "\"| ";
      if (succ.kind == SuccKind::Exit)
        graph << "exit\n";
      else
        graph << "pc" << succ.pc << "\n";
    }
  }
  graph << "```\n";
  for (const auto &stop : stops)
    graph << "\n" << stop << "\n";
  parts.graph = graph.str();

  std::ostringstream cites;
  std::ostringstream steps;
  steps << "The concrete step is the state at the end of the eBPF instruction, "
           "not the state of each IR block.\n\n";
  for (const auto &node : program.nodes) {
    const EbInsn *insn = nullptr;
    for (const auto &candidate : insns) {
      if (candidate.index == node.pc)
        insn = &candidate;
    }
    if (!insn)
      throw std::runtime_error("gate node has no instruction");
    bool walked = false;
    for (const auto &input : inputs) {
      const Step *rocq_step = find_step(*input.rocq, node.pc);
      const Step *alive_step = find_step(*input.alive, node.pc);
      if (!rocq_step && !alive_step)
        continue;
      walked = true;
      steps << "### pc" << node.pc << " " << input.rocq->case_id << "\n\n";
      if (rocq_step) {
        steps << "R_r(pc" << node.pc << ", S, S') for " << input.rocq->case_id
              << ".\n\n";
        steps << "S is " << regs_text(rocq_step->before) << ".\n\n";
        steps << "S' is " << regs_text(rocq_step->after) << ".\n\n";
      } else {
        steps << "Rocq did not record pc" << node.pc << " for "
              << input.rocq->case_id << ".\n\n";
      }
      if (alive_step) {
        steps << "R_a(pc" << node.pc << ", S, S') for " << input.alive->case_id
              << ".\n\n";
        steps << "S is " << regs_text(alive_step->before) << ".\n\n";
        steps << "S' is " << regs_text(alive_step->after) << ".\n\n";
      } else {
        steps << "Alive2 did not record pc" << node.pc << " for "
              << input.alive->case_id << ".\n\n";
      }
      if (rocq_step) {
        auto sentence = undef_sentence(rocq_step->after);
        if (!sentence.empty())
          steps << sentence << "\n\n";
      }
      if (rocq_step && alive_step && rocq_step->status == alive_step->status)
        steps << "Status is " << status_name(rocq_step->status) << ".\n\n";
      else {
        if (rocq_step)
          steps << "Rocq status is " << status_name(rocq_step->status) << ".\n\n";
        if (alive_step)
          steps << "Alive2 status is " << status_name(alive_step->status)
                << ".\n\n";
      }
      if (rocq_step && alive_step &&
          pc_text(rocq_step->pc_after) == pc_text(alive_step->pc_after)) {
        steps << "PC update is pc" << node.pc << " to "
              << pc_text(rocq_step->pc_after) << ".\n\n";
      } else {
        if (rocq_step)
          steps << "Rocq PC update is pc" << node.pc << " to "
                << pc_text(rocq_step->pc_after) << ".\n\n";
        if (alive_step)
          steps << "Alive2 PC update is pc" << node.pc << " to "
                << pc_text(alive_step->pc_after) << ".\n\n";
      }
      const Trace *memory_trace = rocq_step ? input.rocq : input.alive;
      const char *memory =
          memory_trace->memory == MemorySummary::Empty ? "empty" : "changed";
      if (std::holds_alternative<EbJmp>(insn->op) &&
          std::get<EbJmp>(insn->op).op == EbJmp::Exit) {
        steps << "Memory effect is " << memory
              << ". `exec_ret` on an empty call stack returns Next with PC set "
                 "to Vnullptr and the same m. The return value is r0.\n\n";
      } else {
        steps << "Memory effect is " << memory
              << ". That is the m returned by Next in `" << next_def(*insn)
              << "`.\n\n";
      }
      if (rocq_step && alive_step &&
          ret_text(rocq_step->return_value) == ret_text(alive_step->return_value))
        steps << "Return value is " << ret_text(rocq_step->return_value) << ".\n\n";
      else {
        if (rocq_step)
          steps << "Rocq return value is " << ret_text(rocq_step->return_value)
                << ".\n\n";
        if (alive_step)
          steps << "Alive2 return value is " << ret_text(alive_step->return_value)
                << ".\n\n";
      }
      if (rocq_step)
        steps << "Source bytes are " << rocq_step->source_hex << ".\n\n";
      else if (alive_step)
        steps << "Source bytes are " << alive_step->source_hex << ".\n\n";
    }
    if (!walked)
      throw std::runtime_error("no input walked pc" + std::to_string(node.pc));

    cites << "Citation for pc" << node.pc << ". `Definition find_instr` in "
             "ebpfDecoder.v. ";
    auto names = cite_names(*insn);
    for (size_t i = 0; i < names.size(); ++i) {
      if (i)
        cites << ", ";
      cites << "`Definition " << names[i] << "`";
    }
    cites << " in ebpfBinSem.v. This note names the definitions. Rocq did not "
             "print this term.\n\n";
    if (const auto *jmp = std::get_if<EbJmp>(&insn->op)) {
      if (jmp->op == EbJmp::Jgt && jmp->src == EbSrc::Imm && jmp->imm == 10) {
        cites << "`eval_cmp_static` is not the result for immediate 10. Its W64 "
                 "GT Unsigned arm matches only the immediate -1. `exec_jmpcmp` "
                 "tries `eval_cmp_static`, then `eval_cmp64` for W64.\n\n";
      }
    }
  }
  parts.cites = cites.str();
  parts.steps = steps.str();

  for (const auto &node : program.nodes) {
    auto id = "pc" + std::to_string(node.pc);
    if (!has_id(parts.graph, id) || !has_id(parts.cites, id) ||
        !has_id(parts.steps, id))
      throw std::runtime_error("node " + id +
                               " is missing from the graph, the citation, or "
                               "the concrete step");
  }
  return parts;
}

std::string fence_for(const std::string &body) {
  std::string fence = "```";
  while (body.find(fence) != std::string::npos)
    fence.push_back('`');
  return fence;
}

void fenced(std::ostream &out, const std::string &body) {
  auto fence = fence_for(body);
  out << fence << "\n" << body;
  if (body.empty() || body.back() != '\n')
    out << "\n";
  out << fence << "\n";
}

void expr_block(std::ostream &out, const char *label, const smt::expr &expr) {
  std::ostringstream shown;
  shown << expr;
  out << label << "\n\n<!-- smt-start -->\n";
  fenced(out, shown.str());
  out << "<!-- smt-end -->\n\n";
}

std::vector<std::pair<uint8_t, std::string>> input_names(const Fixture &fixture) {
  std::vector<std::pair<uint8_t, std::string>> names;
  for (auto [reg, bits] : fixture.inputs) {
    (void)bits;
    names.emplace_back(reg, "r" + std::to_string(reg));
  }
  return names;
}

struct Loaded {
  const Trace rocq;
  const Trace alive;
};

Loaded load_pair(const std::filesystem::path &dir, const Fixture &fixture) {
  auto rocq = read_trace(dir / fixture.id / "rocq.trace.json");
  auto alive = read_trace(dir / fixture.id / "alive2.trace.json");
  if (rocq.bytes_hex != fixture.bytes_hex || alive.bytes_hex != fixture.bytes_hex)
    throw std::runtime_error(std::string(fixture.id) + " bytes are not the fixture");
  return {std::move(rocq), std::move(alive)};
}

void require_agree(const Loaded &row, const char *id) {
  if (first_divergence(row.rocq, row.alive))
    throw std::runtime_error(std::string(id) + " traces do not agree");
}

std::string show_exec(const char *title, const EbExec &exec, bool jgt_value) {
  std::ostringstream out;
  out << "### " << title << "\n\n";
  out << "Decoded instructions.\n\n";
  fenced(out, exec.decoded);
  out << "\nAlive2 block cfg from `execute_ebpf`.\n\n";
  fenced(out, exec.cfg);
  out << "\nAlive2 IR from `execute_ebpf`.\n\n";
  fenced(out, exec.ir);
  out << "\n`execute_ebpf` memory field.\n\n";
  fenced(out, exec.memory);
  out << "\n`value` is the path-merged return, not the concrete r0 of ";
  out << (jgt_value ? "either JGT input" : "this input") << ".\n\n";
  expr_block(out, "`defined` is function_domain.", exec.defined);
  expr_block(out, "`non_poison` is the Alive2 return non_poison expression.",
             exec.non_poison);
  expr_block(out, "`returned` is the Alive2 return_domain expression.",
             exec.returned);
  expr_block(out, "`value` is the path-merged return.", exec.value);
  return out.str();
}

void usage() {
  std::cerr << "usage: ebpf-exhibit --traces DIR --out FILE\n";
}

}

int main(int argc, char **argv) {
  std::string traces;
  std::string out_path;
  for (int i = 1; i < argc; ++i) {
    std::string arg = argv[i];
    if (arg == "--traces" && i + 1 < argc)
      traces = argv[++i];
    else if (arg == "--out" && i + 1 < argc)
      out_path = argv[++i];
    else {
      usage();
      return 2;
    }
  }
  if (traces.empty() || out_path.empty()) {
    usage();
    return 2;
  }

  try {
    const Fixture &jgt11_fix = need_fixture("jgt64-11");
    const Fixture &jgt10_fix = need_fixture("jgt64-10");
    const Fixture &div_fix = need_fixture("div64-7-0");
    const Fixture &ub_fix = need_fixture("div64-7-0-div-zero-as-ub");
    if (std::string(jgt11_fix.bytes_hex) != jgt10_fix.bytes_hex)
      throw std::runtime_error("jgt fixtures do not share bytes");
    if (std::string(div_fix.bytes_hex) != ub_fix.bytes_hex)
      throw std::runtime_error("div fixtures do not share bytes");

    std::filesystem::path dir(traces);
    Loaded jgt11 = load_pair(dir, jgt11_fix);
    Loaded jgt10 = load_pair(dir, jgt10_fix);
    Loaded div = load_pair(dir, div_fix);
    Loaded ub = load_pair(dir, ub_fix);
    require_agree(jgt11, "jgt64-11");
    require_agree(jgt10, "jgt64-10");
    require_agree(div, "div64-7-0");
    auto ub_found = first_divergence(ub.rocq, ub.alive);
    if (!ub_found || !negative_holds(*ub_found) ||
        ub_found->line != "pc 1 status alive2=UB rocq=NEXT")
      throw std::runtime_error("div-zero-as-ub divergence is not the expected line");

    const std::filesystem::path theories =
        std::filesystem::path(SEMANTICS_DIR) / "theories";
    const char *decoder_names[] = {"find_instr"};
    const char *sem_names[] = {
        "exec_instr", "exec_alu",     "eval_alu64", "eval_div_u64",
        "nextinstr",  "exec_jmpcmp",  "eval_cmp_static", "eval_cmp64",
        "exec_jmp64", "exec_ret"};
    for (const char *name : decoder_names) {
      if (!defines_name(theories / "ebpfDecoder.v", name))
        throw std::runtime_error(std::string("missing Definition ") + name);
    }
    for (const char *name : sem_names) {
      if (!defines_name(theories / "ebpfBinSem.v", name))
        throw std::runtime_error(std::string("missing Definition ") + name);
    }

    // Returned smt::expr values are Z3 ASTs. They need this context until printed.
    smt::smt_initializer smt;
    auto jgt_exec = execute_ebpf(parse_hex(jgt11_fix.bytes_hex),
                                 input_names(jgt11_fix), 1, LiftBug::None);
    auto div_exec = execute_ebpf(parse_hex(div_fix.bytes_hex), input_names(div_fix),
                                 1, LiftBug::None);
    auto ub_exec = execute_ebpf(parse_hex(div_fix.bytes_hex), input_names(div_fix),
                                1, LiftBug::DivZeroAsUb);
    if (div_exec.ir.find("icmp ") == std::string::npos ||
        div_exec.ir.find("udiv ") == std::string::npos ||
        div_exec.ir.find("phi ") == std::string::npos)
      throw std::runtime_error(
          "guarded div IR is missing the zero icmp, udiv block, or merge phi");
    if (ub_exec.ir.find("udiv ") == std::string::npos)
      throw std::runtime_error("mutation IR has no raw udiv");

    auto jgt_insns = decode_ebpf(parse_hex(jgt11_fix.bytes_hex));
    Gate jgt_gate = gate(jgt_insns, regs_from_inputs(jgt11_fix.inputs));
    if (jgt_gate.kind != GateKind::Ready)
      throw std::runtime_error("jgt fixture was rejected");
    bool two = false;
    for (const auto &node : jgt_gate.nodes) {
      if (node.pc == 1 && node.succs.size() == 2 &&
          node.succs[0].kind == SuccKind::Jump &&
          node.succs[1].kind == SuccKind::Fall)
        two = true;
    }
    if (!two)
      throw std::runtime_error("jgt pc 1 does not have two successors");
    const Step *taken = find_step(jgt11.rocq, 1);
    const Step *not_taken = find_step(jgt10.rocq, 1);
    if (!taken || !not_taken ||
        pc_text(taken->pc_after) == pc_text(not_taken->pc_after))
      throw std::runtime_error("jgt traces do not mark different successors");

    auto div_insns = decode_ebpf(parse_hex(div_fix.bytes_hex));
    Gate div_gate = gate(div_insns, regs_from_inputs(div_fix.inputs));
    if (div_gate.kind != GateKind::Ready)
      throw std::runtime_error("div fixture was rejected");

    std::string ub_stop;
    for (const auto &step : ub.alive.steps) {
      if (step.status == StepStatus::Ub)
        ub_stop = "div64-7-0-div-zero-as-ub stops at pc" +
                  std::to_string(step.pc.index) +
                  ". The static fall-through stays.";
    }
    if (ub_stop.empty())
      throw std::runtime_error("ub trace has no stop");

    Parts jgt_parts = build_parts(
        jgt_gate, jgt_insns, {{&jgt11.rocq, &jgt11.alive}, {&jgt10.rocq, &jgt10.alive}},
        {&jgt11.rocq, &jgt10.rocq}, {});
    Parts div_parts = build_parts(
        div_gate, div_insns, {{&div.rocq, &div.alive}, {&ub.rocq, &ub.alive}},
        {&div.rocq}, {ub_stop});

    std::ostringstream md;
    md << "# Exhibit\n\n";
    md << "Run `alive2/exhibit/regen.sh` from the repository root.\n\n";
    md << "## Why the link line stays\n\n";
    md << "ebpf-concrete does not call smt:: or Z3. It still links libir, "
          "libsmt, libtools, libutil, and libz3 because alive2_link is shared "
          "with ebpf_test. ebpf_lift.cpp builds IR instructions whose methods "
          "live in instr.cpp. instr.cpp references IR::State. state.cpp calls "
          "smt::Solver. smt::expr is a Z3 AST. Dropping libsmt or Z3 leaves "
          "those symbols undefined. A second helper that still links those "
          "libraries does not remove them.\n\n";
    md << "## Missing from the Alive2 step\n\n";
    md << "These fields are not in the result of `execute_ebpf`. The list is "
          "not filled in.\n\n";
    md << "- pc-indexed symbolic pre-state and post-state for r0-r10\n";
    md << "- the compare as its own smt::expr\n";
    md << "- the path condition at that pc (getPath dies with IR::State)\n";
    md << "- per-instruction symbolic UB\n";
    md << "- memory before and after as expressions\n";
    md << "- phi operands as data\n\n";

    md << "## JGT64\n\n";
    md << "Bytes from fixture `jgt64-11`, the same bytes as `jgt64-10`.\n\n";
    md << "`" << jgt11.rocq.bytes_hex << "`\n\n";
    md << show_exec("JGT64 execute_ebpf", jgt_exec, true);
    md << "### Graph\n\n";
    md << "Edges come from the gate. A trace may label an edge. It does not "
          "add or drop one.\n\n";
    md << jgt_parts.graph << "\n";
    md << "### Rocq citations\n\n" << jgt_parts.cites;
    md << "### Concrete steps\n\n" << jgt_parts.steps;

    md << "## DIV64\n\n";
    md << "Bytes from fixture `div64-7-0`, the same bytes as "
          "`div64-7-0-div-zero-as-ub`.\n\n";
    md << "`" << div.rocq.bytes_hex << "`\n\n";
    md << show_exec("DIV64 guarded execute_ebpf", div_exec, false);
    md << "The guarded print has the zero icmp, the udiv block, and the merge "
          "phi. One eBPF div is several IR blocks. The concrete step is still "
          "the end of that eBPF instruction.\n\n";
    md << show_exec("DIV64 div-zero-as-ub execute_ebpf", ub_exec, false);
    md << "The mutation print has a raw udiv.\n\n";
    md << "### Graph\n\n";
    md << "Edges come from the gate. A trace may label an edge. It does not "
          "add or drop one.\n\n";
    md << div_parts.graph << "\n";
    md << "### Rocq citations\n\n" << div_parts.cites;
    md << "### Concrete steps\n\n" << div_parts.steps;

    md << "## Comparison\n\n";
    md << "Concrete PASS is this input only. It is not a proof for all inputs.\n\n";
    const char *not_est =
        "This input is not all inputs. See Missing from the Alive2 step.";
    const char *jgt_struct =
        "pc1 has two successors. jgt64-11 and jgt64-10 mark different ones.";
    md << "### JGT64 by instruction\n\n";
    append_insn_table(md, jgt_gate, jgt_insns,
                      {{&jgt11.rocq, &jgt11.alive}, {&jgt10.rocq, &jgt10.alive}},
                      jgt_struct, "", "");
    md << "### DIV64 by instruction\n\n";
    append_insn_table(md, div_gate, div_insns,
                      {{&div.rocq, &div.alive}, {&ub.rocq, &ub.alive}},
                      "The guarded IR has the zero icmp, the udiv block, and the "
                      "merge phi.",
                      "div64-7-0-div-zero-as-ub", ub_found->line);
    md << "### By input\n\n";
    md << "| Input | Concrete PASS | Structural Match | Not Established |\n";
    md << "| --- | --- | --- | --- |\n";
    md << "| jgt64-11 | Yes. This input's traces agree. | " << jgt_struct
       << " | " << not_est << " |\n";
    md << "| jgt64-10 | Yes. This input's traces agree. | " << jgt_struct
       << " | " << not_est << " |\n";
    md << "| div64-7-0 | Yes. This input's traces agree. | The guarded IR has "
          "the zero icmp, the udiv block, and the merge phi. | "
       << not_est << " |\n";
    md << "| div64-7-0-div-zero-as-ub | No. " << ub_found->line << " | "
       << ub_found->line << " | " << not_est << " |\n";

    auto dest = std::filesystem::path(out_path);
    std::filesystem::create_directories(dest.parent_path());
    auto tmp = dest;
    tmp += ".tmp";
    {
      std::ofstream file(tmp, std::ios::binary | std::ios::trunc);
      if (!file)
        throw std::runtime_error("cannot write exhibit");
      file << md.str();
      file.flush();
      if (!file)
        throw std::runtime_error("cannot flush exhibit");
    }
    if (std::rename(tmp.c_str(), dest.c_str()) != 0)
      throw std::runtime_error("cannot replace exhibit");
  } catch (const std::exception &ex) {
    std::cerr << ex.what() << "\n";
    return 1;
  }
  return 0;
}
