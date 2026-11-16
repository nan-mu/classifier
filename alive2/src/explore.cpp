#include "ir/function.h"
#include "ir/globals.h"
#include "ir/instr.h"
#include "ir/state.h"
#include "ir/type.h"
#include "smt/expr.h"
#include "smt/smt.h"
#include "tools/alive_parser.h"
#include "util/config.h"
#include "util/symexec.h"

#include <CommonCrypto/CommonDigest.h>

#include <fstream>
#include <iostream>
#include <optional>
#include <sstream>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

using namespace IR;

namespace {

struct Term {
  std::string id;
  std::string op;
  std::string sort;
  int width = -1;
  std::vector<std::string> args;
  std::string digits;
  std::string display;
  std::string poison;
};

struct Node {
  std::string id;
  std::string function;
  std::string block;
  std::string instr;
  std::string text;
  unsigned unroll = 0;
  std::string state;
  std::string path;
  std::string term;
  std::string unsupported_reason;
};

struct Edge {
  std::string id;
  std::string from;
  std::string to;
  std::string kind;
  std::string guard;
};

std::string json_string(std::string_view text) {
  std::string out = "\"";
  for (unsigned char c : text) {
    if (c == '"' || c == '\\') {
      out.push_back('\\');
      out.push_back(static_cast<char>(c));
    } else if (c == '\n') {
      out += "\\n";
    } else if (c < 0x20) {
      char buf[8];
      std::snprintf(buf, sizeof buf, "\\u%04x", c);
      out += buf;
    } else {
      out.push_back(static_cast<char>(c));
    }
  }
  out.push_back('"');
  return out;
}

std::string sha256_file(const std::string &path) {
  std::ifstream in(path, std::ios::binary);
  std::ostringstream buf;
  buf << in.rdbuf();
  auto bytes = buf.str();
  unsigned char hash[CC_SHA256_DIGEST_LENGTH];
  CC_SHA256(bytes.data(), static_cast<CC_LONG>(bytes.size()), hash);
  static const char *hexd = "0123456789abcdef";
  std::string out(CC_SHA256_DIGEST_LENGTH * 2, '0');
  for (int i = 0; i < CC_SHA256_DIGEST_LENGTH; ++i) {
    out[i * 2] = hexd[hash[i] >> 4];
    out[i * 2 + 1] = hexd[hash[i] & 0xf];
  }
  return out;
}

std::string read_file(const std::string &path) {
  std::ifstream in(path, std::ios::binary);
  if (!in)
    throw std::runtime_error("cannot read " + path);
  std::ostringstream buf;
  buf << in.rdbuf();
  return buf.str();
}

void configure_pure_alu() {
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
  bits_byte = 8;
  bits_poison_per_byte = 1;
  bits_program_pointer = 64;
  little_endian = true;
}

unsigned unroll_index(std::string_view name) {
  auto pos = name.rfind('#');
  if (pos == std::string_view::npos || pos + 1 >= name.size())
    return 0;
  unsigned n = 0;
  for (char c : name.substr(pos + 1)) {
    if (c < '0' || c > '9')
      return 0;
    n = n * 10 + static_cast<unsigned>(c - '0');
  }
  return n;
}

struct Terms {
  std::vector<Term> items;
  std::unordered_map<std::string, std::string> by_key;

  std::string add(Term term) {
    std::string key = term.op + "|" + term.sort + "|" + term.digits + "|" + term.display;
    for (auto &arg : term.args)
      key += "|" + arg;
    auto found = by_key.find(key);
    if (found != by_key.end())
      return found->second;
    term.id = "t" + std::to_string(items.size());
    by_key.emplace(key, term.id);
    items.push_back(std::move(term));
    return items.back().id;
  }

  std::string boolean(bool value) {
    Term term;
    term.op = value ? "true" : "false";
    term.sort = "bool";
    return add(std::move(term));
  }

  std::string from_expr(const smt::expr &expr) {
    std::ostringstream shown;
    shown << expr;
    if (expr.isTrue())
      return boolean(true);
    if (expr.isFalse())
      return boolean(false);
    Term term;
    term.display = shown.str();
    if (expr.isBV() && expr.isConst()) {
      term.op = "bv";
      term.sort = "bv";
      term.width = static_cast<int>(expr.bits());
      term.digits = std::string(expr.numeral_string());
      term.display.clear();
      return add(std::move(term));
    }
    if (expr.isBV()) {
      term.op = "opaque";
      term.sort = "bv";
      term.width = static_cast<int>(expr.bits());
      return add(std::move(term));
    }
    term.op = "opaque";
    term.sort = "bool";
    return add(std::move(term));
  }
};

const char *usage() {
  return "usage: alive2-explore run <program.alive> --initial <initial.json> "
         "--unroll <k> --graph-out <graph.json> [--origin <origin.json>] "
         "[--environment <environment.json>] [--budget-steps <n>]\n";
}

} // namespace

int main(int argc, char **argv) {
  try {
    if (argc < 3 || std::string(argv[1]) != "run") {
      std::cerr << usage();
      return 2;
    }
    std::string program_path = argv[2];
    std::string initial_path;
    std::string graph_path;
    std::optional<std::string> origin_path;
    std::optional<std::string> environment_path;
    unsigned unroll = 0;
    bool saw_unroll = false;
    unsigned budget_steps = 10000;
    for (int i = 3; i < argc; ++i) {
      std::string flag = argv[i];
      auto need = [&](const char *name) {
        if (i + 1 >= argc)
          throw std::runtime_error(std::string("missing value for ") + name);
        return std::string(argv[++i]);
      };
      if (flag == "--initial")
        initial_path = need("--initial");
      else if (flag == "--unroll") {
        saw_unroll = true;
        unroll = static_cast<unsigned>(std::stoul(need("--unroll")));
      } else if (flag == "--graph-out")
        graph_path = need("--graph-out");
      else if (flag == "--origin")
        origin_path = need("--origin");
      else if (flag == "--environment")
        environment_path = need("--environment");
      else if (flag == "--budget-steps")
        budget_steps = static_cast<unsigned>(std::stoul(need("--budget-steps")));
      else
        throw std::runtime_error("unknown argument " + flag);
    }
    if (initial_path.empty() || graph_path.empty() || !saw_unroll)
      throw std::runtime_error(usage());

    smt::smt_initializer smt_init;
    std::string initial = read_file(initial_path);
    if (initial.find('{') == std::string::npos)
      throw std::runtime_error("INITIAL_STATE_INVALID");
    if (origin_path)
      read_file(*origin_path);
    if (environment_path)
      read_file(*environment_path);

    tools::parser_initializer parser_init;
    auto parsed = tools::parse_single(read_file(program_path));
    std::string fn_name = std::move(parsed.first);
    Function fn = std::move(parsed.second);

    configure_pure_alu();
    util::config::src_unroll_cnt = unroll;
    fn.unroll(unroll);

    State::resetGlobals();
    State state(fn, true);
    util::sym_exec_init(state);

    Terms terms;
    std::string truth = terms.boolean(true);
    std::vector<Node> nodes;
    std::vector<Edge> edges;
    std::vector<std::string> instr_ids;
    std::vector<std::string> instr_text;
    std::unordered_map<std::string, std::string> bb_first;
    std::unordered_map<std::string, std::string> bb_last;
    std::unordered_map<std::string, const Instr *> bb_term;
    std::string first_node;
    std::vector<std::string> assumptions;
    bool saw_sink = false;
    bool saw_resource = false;

    Node entry;
    entry.id = "n0";
    entry.function = fn_name;
    entry.block = "entry";
    entry.instr = "";
    entry.text = "entry";
    entry.state = "normal";
    entry.path = truth;
    entry.term = truth;
    nodes.push_back(entry);

    unsigned steps = 0;
    for (auto &bb : fn.getBBs()) {
      if (bb->getName() == "#init")
        continue;
      if (steps >= budget_steps) {
        saw_resource = true;
        break;
      }
      if (!state.startBB(*bb)) {
        assumptions.push_back(std::string("startBB returned false for ") + std::string(bb->getName()));
        continue;
      }
      std::string previous;
      bool first = true;
      for (auto &instr : bb->instrs()) {
        if (steps >= budget_steps) {
          saw_resource = true;
          break;
        }
        ++steps;
        auto &val = state.exec(instr);
        std::ostringstream printed;
        instr.print(printed);
        std::string iid = "i" + std::to_string(instr_ids.size());
        instr_ids.push_back(iid);
        instr_text.push_back(printed.str());

        Node node;
        node.id = "n" + std::to_string(nodes.size());
        node.function = fn_name;
        node.block = std::string(bb->getName());
        node.instr = iid;
        node.text = printed.str();
        node.unroll = unroll_index(bb->getName());
        node.path = truth;
        node.term = terms.from_expr(val.val.value);
        if (auto *ret = dynamic_cast<const Return *>(&instr)) {
          if (!ret->operands().empty() && ret->operands()[0])
            node.term = terms.from_expr(state[*ret->operands()[0]].value);
        }
        if (val.val.non_poison.isFalse())
          node.unsupported_reason = "poison";
        if (!val.domain.isTrue())
          node.state = "ub";
        else if (dynamic_cast<const Return *>(&instr))
          node.state = "exit";
        else if (bb->getName() == "#sink") {
          node.state = "bound_truncated";
          saw_sink = true;
        } else
          node.state = "normal";
        if (first) {
          bb_first.emplace(node.block, node.id);
          if (first_node.empty())
            first_node = node.id;
          first = false;
        }
        if (!previous.empty()) {
          Edge edge;
          edge.id = "e" + std::to_string(edges.size());
          edge.from = previous;
          edge.to = node.id;
          edge.kind = node.state == "exit" ? "exit" : "step";
          edge.guard = truth;
          edges.push_back(edge);
        }
        previous = node.id;
        bb_last[node.block] = node.id;
        if (dynamic_cast<const JumpInstr *>(&instr))
          bb_term[node.block] = &instr;
        nodes.push_back(std::move(node));
      }
    }

    if (!first_node.empty()) {
      Edge edge;
      edge.id = "e" + std::to_string(edges.size());
      edge.from = "n0";
      edge.to = first_node;
      edge.kind = "step";
      edge.guard = truth;
      edges.push_back(edge);
    }

    for (auto &[block, term_instr] : bb_term) {
      auto last = bb_last.find(block);
      if (last == bb_last.end())
        continue;
      if (auto *br = dynamic_cast<const Branch *>(term_instr)) {
        auto link = [&](const BasicBlock &dst, const char *kind, const std::string &guard) {
          auto target = bb_first.find(std::string(dst.getName()));
          if (target == bb_first.end()) {
            assumptions.push_back("no node for target " + std::string(dst.getName()));
            return;
          }
          Edge edge;
          edge.id = "e" + std::to_string(edges.size());
          edge.from = last->second;
          edge.to = target->second;
          edge.kind = dst.getName() == "#sink" ? "boundary" : kind;
          if (edge.kind == "boundary")
            saw_sink = true;
          edge.guard = guard;
          edges.push_back(std::move(edge));
        };
        if (!br->getCond()) {
          link(br->getTrue(), "step", truth);
        } else {
          auto &cond = state[*br->getCond()].value;
          std::string guard = terms.from_expr(cond);
          Term negated;
          negated.op = "not";
          negated.sort = "bool";
          negated.args = {guard};
          std::string neg = terms.add(std::move(negated));
          if (cond.isTrue())
            link(br->getTrue(), "taken", guard);
          else if (cond.isFalse())
            link(*br->getFalse(), "not_taken", neg);
          else {
            link(br->getTrue(), "taken", guard);
            if (br->getFalse())
              link(*br->getFalse(), "not_taken", neg);
          }
        }
      }
    }

    std::vector<std::string> frontier;
    std::vector<std::string> returns;
    for (auto &node : nodes) {
      if (node.state == "bound_truncated")
        frontier.push_back(node.id);
      if (node.state == "exit")
        returns.push_back(node.id);
    }
    if (saw_resource && !nodes.empty())
      frontier.push_back(nodes.back().id);

    std::string truncation = "none";
    std::string reason;
    if (saw_sink) {
      truncation = "bound";
      reason = "unroll bound reached the Alive2 sink";
    } else if (saw_resource) {
      truncation = "resource";
      reason = "step budget exhausted";
    }

    std::ofstream out(graph_path);
    if (!out)
      throw std::runtime_error("cannot write " + graph_path);
    std::string ir_hash = sha256_file(program_path);
    std::string initial_hash = sha256_file(initial_path);
    out << "{\n";
    out << "  \"schema\": \"alive2-state-graph\",\n";
    out << "  \"schema_version\": 1,\n";
    out << "  \"fixture\": false,\n";
    out << "  \"run\": {\"id\": " << json_string("run-" + ir_hash.substr(0, 12))
        << ", \"status\": \"finished\", \"initial_id\": " << json_string(initial_hash)
        << ", \"engine_pin\": \"alive2 adacbd5180ccf95075e9867c4f0c259f59c9fef2\""
        << ", \"unroll_bound\": " << unroll
        << ", \"budgets\": {\"steps\": " << budget_steps << "}"
        << ", \"truncation\": {\"kind\": " << json_string(truncation)
        << ", \"reason\": " << json_string(reason) << "}},\n";
    out << "  \"program\": {\"ir_hash\": " << json_string(ir_hash)
        << ", \"functions\": [{\"id\": \"fn0\", \"name\": " << json_string(fn_name) << "}]"
        << ", \"instructions\": [";
    for (size_t i = 0; i < instr_ids.size(); ++i) {
      if (i)
        out << ", ";
      out << "{\"id\": " << json_string(instr_ids[i]) << ", \"text\": " << json_string(instr_text[i]) << "}";
    }
    out << "], \"origin\": null},\n";
    auto unsupported = [](const char *why) {
      return std::string("{\"unsupported\": ") + json_string(why) + "}";
    };
    out << "  \"environment\": {"
        << "\"main_program\": " << unsupported("generic IR run has no eBPF code table")
        << ", \"code_table\": " << unsupported("generic IR run has no eBPF code table")
        << ", \"jump_table\": " << unsupported("generic IR run has no jump table")
        << ", \"addr_map\": " << unsupported("generic IR run has no address map")
        << ", \"helpers\": " << unsupported("generic IR run has no helper contract")
        << ", \"input_objects\": " << unsupported("generic IR run has no input memory objects")
        << ", \"global_reserved\": {\"threading\": \"single\""
        << ", \"thread_pool\": {\"status\": \"unsupported\", \"reason\": \"single thread only\"}"
        << ", \"env\": {\"status\": \"unsupported\", \"reason\": \"single thread only\"}"
        << ", \"gm\": {\"status\": \"unsupported\", \"reason\": \"single thread only\"}"
        << ", \"atom_bit\": {\"status\": \"unsupported\", \"reason\": \"single thread only\"}}},\n";
    out << "  \"terms\": [";
    for (size_t i = 0; i < terms.items.size(); ++i) {
      auto &term = terms.items[i];
      if (i)
        out << ", ";
      out << "{\"id\": " << json_string(term.id) << ", \"op\": " << json_string(term.op)
          << ", \"sort\": {\"kind\": " << json_string(term.sort);
      if (term.width >= 0)
        out << ", \"width\": " << term.width;
      out << "}, \"args\": [";
      for (size_t a = 0; a < term.args.size(); ++a) {
        if (a)
          out << ", ";
        out << json_string(term.args[a]);
      }
      out << "]";
      if (!term.digits.empty())
        out << ", \"digits\": " << json_string(term.digits);
      if (!term.display.empty())
        out << ", \"display\": " << json_string(term.display);
      out << "}";
    }
    out << "],\n";
    out << "  \"memories\": [{\"id\": \"mem0\", \"next_block\": \"0\", \"blocks\": [{"
        << "\"id\": \"none\", \"unsupported\": \"this build does not dump Alive2 memory bytes\"}]}],\n";
    out << "  \"nodes\": [";
    for (size_t i = 0; i < nodes.size(); ++i) {
      auto &node = nodes[i];
      if (i)
        out << ", ";
      out << "{\"id\": " << json_string(node.id)
          << ", \"location\": {\"function\": " << json_string(node.function)
          << ", \"block\": " << json_string(node.block)
          << ", \"instr\": " << json_string(node.instr) << "}"
          << ", \"origin_location\": null, \"unroll\": " << node.unroll
          << ", \"state\": " << json_string(node.state)
          << ", \"path_condition\": " << json_string(node.path)
          << ", \"ir_state\": {\"function\": " << json_string(node.function)
          << ", \"block\": " << json_string(node.block)
          << ", \"instr\": " << json_string(node.instr)
          << ", \"values\": [{\"instr\": " << json_string(node.instr)
          << ", \"term\": " << json_string(node.term) << "}]"
          << ", \"memory_id\": \"mem0\", \"memory_status\": \"unsupported\""
          << ", \"exec_status\": " << json_string(node.state) << "}"
          << ", \"rocq_ebpf\": null, \"evidence_ids\": []";
      if (!node.unsupported_reason.empty())
        out << ", \"unsupported_reason\": " << json_string(node.unsupported_reason);
      out << "}";
    }
    out << "],\n  \"edges\": [";
    for (size_t i = 0; i < edges.size(); ++i) {
      auto &edge = edges[i];
      if (i)
        out << ", ";
      out << "{\"id\": " << json_string(edge.id)
          << ", \"from\": " << json_string(edge.from)
          << ", \"to\": " << json_string(edge.to)
          << ", \"kind\": " << json_string(edge.kind)
          << ", \"guard\": " << json_string(edge.guard)
          << ", \"ir_span\": [], \"events\": [], \"changed\": [], \"evidence_ids\": []}";
    }
    out << "],\n  \"coverage\": {\"return_domain\": [";
    for (size_t i = 0; i < returns.size(); ++i) {
      if (i)
        out << ", ";
      out << json_string(returns[i]);
    }
    out << "], \"sink_domain\": [";
    for (size_t i = 0; i < frontier.size(); ++i) {
      if (i)
        out << ", ";
      out << json_string(frontier[i]);
    }
    out << "], \"assumptions\": [";
    for (size_t i = 0; i < assumptions.size(); ++i) {
      if (i)
        out << ", ";
      out << json_string(assumptions[i]);
    }
    out << "], \"frontier\": [";
    bool frontier_only_bound = saw_sink && !saw_resource;
    size_t frontier_n = 0;
    for (auto &node : nodes) {
      if (node.state != "bound_truncated")
        continue;
      if (frontier_n++)
        out << ", ";
      out << json_string(node.id);
    }
    if (!frontier_only_bound && saw_resource && !nodes.empty()) {
      if (frontier_n)
        out << ", ";
      out << json_string(nodes.back().id);
    }
    out << "], \"all_inputs_covered\": \"not_established\"},\n";
    out << "  \"evidence\": [{\"id\": \"ev-observer\", \"kind\": \"implementation_proof\","
        << " \"status\": \"pending\", \"scope\": [{\"kind\": \"file\", \"id\": "
        << json_string(program_path) << "}],"
        << " \"note\": \"The C++ observer that walks State::exec is not a Rocq proof.\"}]\n";
    out << "}\n";

    if (origin_path) {
      std::cerr << "ORIGIN_PRESENT_BUT_UNUSED " << *origin_path << "\n";
    }
    (void)environment_path;
    return 0;
  } catch (const tools::ParseException &err) {
    std::cerr << "IR_PARSE_ERROR:" << err.lineno << ": " << err.str << "\n";
    return 2;
  } catch (const std::exception &err) {
    std::cerr << err.what() << "\n";
    return 2;
  }
}
