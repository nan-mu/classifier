#include "ir/constant.h"
#include "ir/function.h"
#include "ir/globals.h"
#include "ir/instr.h"
#include "ir/state.h"
#include "ir/type.h"
#include "smt/expr.h"
#include "smt/smt.h"
#include "smt/ctx.h"
#include <z3.h>
#include <algorithm>
#include "alive_file.h"
#include "explore_initial.h"
#include "util/config.h"
#include "util/symexec.h"

#include <openssl/evp.h>
#include <charconv>
#include <unistd.h>

#include <filesystem>
#include <json-c/json.h>
#include <set>
#include <map>
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
  std::string sort_json;
  std::string symbol;
  std::string parameters = "[]";
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
  std::string definedness;
  std::string preconditions, axioms, call_preconditions;
  std::string memory;
  std::string origin = "null", snapshot_kind = "native_after_instruction";
  std::string returned_values = "[]", returned_memories = "[]";
  struct Binding { std::string name, type, term, non_poison, domain; };
  std::vector<Binding> values;
};

struct Edge {
  std::string id;
  std::string from;
  std::string to;
  std::string kind;
  std::string guard;
  bool native_jump = false;
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

std::string sha256(const std::string &bytes) {
  unsigned char hash[EVP_MAX_MD_SIZE];
  unsigned length = 0;
  if (!EVP_Digest(bytes.data(), bytes.size(), hash, &length, EVP_sha256(), nullptr))
    throw std::runtime_error("SHA256 failed");
  static const char *hexd = "0123456789abcdef";
  std::string out(length * 2, '0');
  for (unsigned i = 0; i < length; ++i) {
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
  std::unordered_map<unsigned, std::string> by_ast;
  std::vector<Z3_ast> retained;
  ~Terms() { for (auto ast : retained) Z3_dec_ref(smt::ctx(), ast); }

  std::string add(Term term) {
    static const std::set<std::string> commutative = {
      "and", "or", "xor", "eq", "distinct", "bvadd", "bvmul",
      "bvand", "bvor", "bvxor", "bvnand", "bvnor", "bvxnor"
    };
    if (commutative.contains(term.op)) std::sort(term.args.begin(), term.args.end());
    std::string key = "[" + json_string(term.op) + "," + json_string(term.sort_json) + "," + json_string(term.sort) + "," + std::to_string(term.width) + "," + json_string(term.digits) + "," + json_string(term.symbol) + "," + term.parameters + "," + json_string(term.op == "unsupported" ? term.display : "");
    for (auto &arg : term.args) key += "," + json_string(arg);
    key += "]";
    auto found = by_key.find(key);
    if (found != by_key.end())
      return found->second;
    term.id = "t" + sha256(key);
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

  static std::string sort_of(Z3_sort sort) {
    switch (Z3_get_sort_kind(smt::ctx(), sort)) {
    case Z3_BOOL_SORT: return "{\"kind\":\"bool\"}";
    case Z3_BV_SORT: return "{\"kind\":\"bv\",\"width\":" + std::to_string(Z3_get_bv_sort_size(smt::ctx(), sort)) + "}";
    case Z3_ARRAY_SORT:
      return "{\"kind\":\"array\",\"domain\":" + sort_of(Z3_get_array_sort_domain(smt::ctx(), sort))
        + ",\"range\":" + sort_of(Z3_get_array_sort_range(smt::ctx(), sort)) + "}";
    default: return "{\"kind\":\"unsupported\",\"native\":" + json_string(Z3_sort_to_string(smt::ctx(), sort)) + "}";
    }
  }

  std::string from_ast(Z3_ast ast) {
    auto id = Z3_get_ast_id(smt::ctx(), ast);
    if (auto it = by_ast.find(id); it != by_ast.end()) return it->second;
    auto result = build_ast(ast);
    Z3_inc_ref(smt::ctx(), ast);
    retained.push_back(ast);
    by_ast.emplace(id, result);
    return result;
  }

  std::string build_ast(Z3_ast ast) {
    Term term;
    term.display = "";
    auto sort = Z3_get_sort(smt::ctx(), ast);
    auto kind = Z3_get_sort_kind(smt::ctx(), sort);
    term.sort = kind == Z3_BOOL_SORT ? "bool" : kind == Z3_BV_SORT ? "bv" : kind == Z3_ARRAY_SORT ? "array" : "unsupported";
    if (kind == Z3_BV_SORT) term.width = Z3_get_bv_sort_size(smt::ctx(), sort);
    term.sort_json = sort_of(sort);
    auto ast_kind = Z3_get_ast_kind(smt::ctx(), ast);
    if (ast_kind == Z3_NUMERAL_AST && kind == Z3_BV_SORT) {
      term.op = "bv";
      term.digits = Z3_get_numeral_string(smt::ctx(), ast);
    } else if (ast_kind == Z3_VAR_AST) {
      term.op = "bound";
      term.digits = std::to_string(Z3_get_index_value(smt::ctx(), ast));
    } else if (ast_kind == Z3_QUANTIFIER_AST && term.sort != "unsupported") {
      term.op = Z3_is_lambda(smt::ctx(), ast) ? "lambda" : Z3_is_quantifier_forall(smt::ctx(), ast) ? "forall" : "exists";
      term.parameters = "[";
      for (unsigned i = 0; i < Z3_get_quantifier_num_bound(smt::ctx(), ast); ++i) {
        if (i) term.parameters += ",";
        term.parameters += sort_of(Z3_get_quantifier_bound_sort(smt::ctx(), ast, i));
      }
      term.parameters += "]";
      term.args.push_back(from_ast(Z3_get_quantifier_body(smt::ctx(), ast)));
    } else if (ast_kind == Z3_APP_AST && term.sort != "unsupported") {
      auto app = Z3_to_app(smt::ctx(), ast);
      auto decl = Z3_get_app_decl(smt::ctx(), app);
      auto op = Z3_get_decl_kind(smt::ctx(), decl);
      if (op == Z3_OP_TRUE || op == Z3_OP_FALSE) return boolean(op == Z3_OP_TRUE);
      auto symbol = Z3_get_decl_name(smt::ctx(), decl);
      auto name = Z3_get_symbol_kind(smt::ctx(), symbol) == Z3_STRING_SYMBOL
        ? std::string(Z3_get_symbol_string(smt::ctx(), symbol)) : std::to_string(Z3_get_symbol_int(smt::ctx(), symbol));
      term.op = op == Z3_OP_EQ ? "eq" : op == Z3_OP_UNINTERPRETED ? "symbol" : name;
      if (op == Z3_OP_UNINTERPRETED) term.symbol = name;
      for (unsigned i = 0; i < Z3_get_app_num_args(smt::ctx(), app); ++i)
        term.args.push_back(from_ast(Z3_get_app_arg(smt::ctx(), app, i)));
      term.parameters = "[";
      for (unsigned i = 0; i < Z3_get_decl_num_parameters(smt::ctx(), decl); ++i) {
        if (i) term.parameters += ",";
        auto parameter_kind = Z3_get_decl_parameter_kind(smt::ctx(), decl, i);
        if (parameter_kind == Z3_PARAMETER_INT)
          term.parameters += std::to_string(Z3_get_decl_int_parameter(smt::ctx(), decl, i));
        else if (parameter_kind == Z3_PARAMETER_SORT)
          term.parameters += sort_of(Z3_get_decl_sort_parameter(smt::ctx(), decl, i));
        else if (parameter_kind == Z3_PARAMETER_SYMBOL) {
          auto parameter = Z3_get_decl_symbol_parameter(smt::ctx(), decl, i);
          term.parameters += json_string(Z3_get_symbol_kind(smt::ctx(), parameter) == Z3_STRING_SYMBOL ? Z3_get_symbol_string(smt::ctx(), parameter) : std::to_string(Z3_get_symbol_int(smt::ctx(), parameter)));
        } else {
          term.op = "unsupported";
          term.parameters += "null";
        }
      }
      term.parameters += "]";
    } else {
      term.op = "unsupported";
      term.display = "native AST kind " + std::to_string(ast_kind) + ", sort " + std::to_string(kind);
      term.symbol = "unsupported-native-ast-" + std::to_string(Z3_get_ast_id(smt::ctx(), ast));
    }
    return add(std::move(term));
  }

  std::string from_expr(const smt::expr &expr) {
    if (expr.isValid()) return from_ast(expr.observerAST());
    Term term;
    term.op = "unsupported";
    term.sort = "unsupported";
    term.display = "native expression is invalid (e.g. void instruction)";
    return add(std::move(term));
  }

};

std::string observe_memory(const Memory &memory, Terms &terms) {
  std::ostringstream out;
  out << "[";
  bool first = true;
  for (auto &block : memory.observeBlocks()) {
    if (!first) out << ",";
    first = false;
    Pointer pointer(memory, block.bid, block.local);
    out << "{\"id\":" << json_string(std::string(block.local ? "local:" : "nonlocal:") + std::to_string(block.bid))
        << ",\"local\":" << (block.local ? "true" : "false")
        << ",\"array\":" << json_string(terms.from_expr(block.array))
        << ",\"byte_encoding\":" << unsigned(block.type)
        << ",\"size\":" << json_string(terms.from_expr(pointer.blockSize()))
        << ",\"alignment\":" << json_string(terms.from_expr(pointer.blockAlignment()))
        << ",\"alive\":" << json_string(terms.from_expr(pointer.isBlockAlive()))
        << ",\"writable\":" << json_string(terms.from_expr(pointer.isWritable()))
        << ",\"allocation_type\":" << json_string(terms.from_expr(pointer.getAllocType()))
        << ",\"undef\":[";
    bool first_undef = true;
    for (auto &undef : block.undef) {
      if (!first_undef) out << ",";
      first_undef = false;
      out << json_string(terms.from_expr(undef));
    }
    out << "]}";
  }
  out << "]";
  return out.str();
}

unsigned positive_integer(const std::string &text) {
  unsigned value = 0;
  auto [end, ec] = std::from_chars(text.data(), text.data() + text.size(), value);
  if (ec != std::errc{} || end != text.data() + text.size() || !value)
    throw std::runtime_error("positive integer required: " + text);
  return value;
}

struct TemporaryOutput {
  std::string path;
  explicit TemporaryOutput(const std::string &target) : path(target + ".tmp.XXXXXX") {
    int fd = mkstemp(path.data());
    if (fd < 0) throw std::runtime_error("cannot create graph temporary file");
    close(fd);
  }
  ~TemporaryOutput() { std::error_code ec; std::filesystem::remove(path, ec); }
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
        unroll = positive_integer(need("--unroll"));
      } else if (flag == "--graph-out")
        graph_path = need("--graph-out");
      else if (flag == "--origin")
        origin_path = need("--origin");
      else if (flag == "--environment")
        environment_path = need("--environment");
      else if (flag == "--budget-steps")
        budget_steps = positive_integer(need("--budget-steps"));
      else
        throw std::runtime_error("unknown argument " + flag);
    }
    if (initial_path.empty() || graph_path.empty() || !saw_unroll)
      throw std::runtime_error(usage());

    smt::smt_initializer smt_init;
    auto initial_text = read_file(initial_path);
    auto initial = explorer::parse_json(initial_text);
    if (environment_path)
      throw std::runtime_error("ENVIRONMENT_UNSUPPORTED: explicit memory/helper environments are not implemented");
    auto program_text = read_file(program_path);
    auto loaded = load_alive_v1(program_text);
    explorer::Json origin(nullptr, json_object_put);
    std::string origin_json = "null";
    std::map<std::string, std::string> origin_definitions;
    std::map<std::string, std::vector<std::string>> origin_statements;
    std::map<std::pair<std::string, std::string>, std::vector<std::string>> origin_block_statements;
    std::map<int64_t, std::string> source_slots;
    auto trim = [](std::string text) {
      const auto begin = text.find_first_not_of(" \t\r\n");
      if (begin == std::string::npos) return std::string();
      return text.substr(begin, text.find_last_not_of(" \t\r\n") - begin + 1);
    };
    if (origin_path) {
      auto origin_text = read_file(*origin_path);
      origin = explorer::parse_json(origin_text);
      if (explorer::string_field(origin.get(), "schema") != "classifier-alive-origin-v1" ||
          explorer::string_field(origin.get(), "alive_sha256") != sha256(program_text))
        throw std::runtime_error("ORIGIN_INVALID: schema or Alive2 hash mismatch");
      auto instructions = explorer::field(origin.get(), "instructions");
      if (!json_object_is_type(instructions, json_type_array)) throw std::runtime_error("ORIGIN_INVALID: instructions must be an array");
      for (size_t row = 0; row < json_object_array_length(instructions); ++row) {
        auto instruction = json_object_array_get_idx(instructions, row);
        auto slot = explorer::field(instruction, "slot");
        if (!json_object_is_type(slot, json_type_int) ||
            !source_slots.emplace(json_object_get_int64(slot), json_object_to_json_string_ext(instruction, JSON_C_TO_STRING_PLAIN)).second)
          throw std::runtime_error("ORIGIN_INVALID: duplicate/invalid source slot");
        auto definitions = explorer::field(instruction, "ir");
        if (!json_object_is_type(definitions, json_type_array)) throw std::runtime_error("ORIGIN_INVALID: ir must be an array");
        json_object *checkpoint = nullptr;
        if (json_object_object_get_ex(instruction, "checkpoint", &checkpoint)) {
          json_object *generated = nullptr;
          if (json_object_object_get_ex(checkpoint, "generated_ir", &generated) && json_object_is_type(generated, json_type_array)) {
            for (size_t g = 0; g < json_object_array_length(generated); ++g) {
              auto line = json_object_array_get_idx(generated, g);
              if (!json_object_is_type(line, json_type_string)) throw std::runtime_error("ORIGIN_INVALID: generated_ir string required");
              origin_statements[trim(json_object_get_string(line))].push_back(json_object_to_json_string_ext(instruction, JSON_C_TO_STRING_PLAIN));
            }
          }
        }
        for (size_t d = 0; d < json_object_array_length(definitions); ++d) {
          auto name = json_object_array_get_idx(definitions, d);
          if (!json_object_is_type(name, json_type_string) ||
              !origin_definitions.emplace(json_object_get_string(name), json_object_to_json_string_ext(instruction, JSON_C_TO_STRING_PLAIN)).second)
            throw std::runtime_error("ORIGIN_INVALID: duplicate/invalid SSA definition");
        }
      }
      json_object *generated = nullptr;
      if (json_object_object_get_ex(origin.get(), "generated_instructions", &generated)) {
        if (!json_object_is_type(generated, json_type_array)) throw std::runtime_error("ORIGIN_INVALID: generated_instructions must be an array");
        for (size_t index = 0; index < json_object_array_length(generated); ++index) {
          auto record = json_object_array_get_idx(generated, index);
          auto slot = explorer::field(record, "slot");
          if (json_object_is_type(slot, json_type_null)) continue;
          if (!json_object_is_type(slot, json_type_int) || !source_slots.contains(json_object_get_int64(slot)))
            throw std::runtime_error("ORIGIN_INVALID: generated instruction source slot missing");
          auto block = explorer::string_field(record, "block");
          auto statement = trim(explorer::string_field(record, "text"));
          origin_block_statements[{"%" + block, statement}].push_back(source_slots.at(json_object_get_int64(slot)));
        }
      }
      origin_json = "{\"ir_hash\":" + json_string(sha256(program_text)) + ",\"sha256\":" + json_string(sha256(origin_text)) +
        ",\"mapping_status\":\"instruction_only\",\"elf_hash_validation\":\"declared_only\",\"metadata\":" + json_object_to_json_string_ext(origin.get(), JSON_C_TO_STRING_PLAIN) + "}";
    }
    Function &fn = loaded.function();
    std::string fn_name = fn.getName();
    auto initialized = explorer::initialize(fn, initial.get());
    configure_alive_execution(fn);
    util::config::disable_undef_input = true;
    util::config::disable_poison_input = true;
    util::config::src_unroll_cnt = unroll;
    if (!unroll) throw std::runtime_error("unroll bound must be positive");
    fn.unroll(unroll);
    fn.topSort();

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
    struct Jump { const BasicBlock *source, *destination; std::string kind, guard; };
    std::vector<Jump> jumps;
    std::string first_node;
    std::vector<std::string> assumptions;
    bool saw_sink = false;
    bool saw_resource = false;

    auto capture_values = [&](Node &node) {
      node.preconditions = terms.from_expr(state.getPre()());
      node.axioms = terms.from_expr(state.getAxioms()());
      node.call_preconditions = terms.from_expr(state.getFnPre());
      std::ostringstream returns, memories;
      returns << "[";
      bool first_return = true;
      if (auto variants = std::get_if<smt::DisjointExpr<StateValue>>(&state.observeReturnValues())) {
        for (auto &[value, domain] : *variants) {
          if (!first_return) returns << ",";
          first_return = false;
          returns << "{\"value\":" << json_string(terms.from_expr(value.value))
            << ",\"non_poison\":" << json_string(terms.from_expr(value.non_poison))
            << ",\"path_condition\":" << json_string(terms.from_expr(domain)) << "}";
        }
      }
      returns << "]";
      node.returned_values = returns.str();
      memories << "[";
      bool first_memory = true;
      if (auto variants = std::get_if<smt::DisjointExpr<Memory>>(&state.observeReturnMemories())) {
        for (auto &[memory, domain] : *variants) {
          if (!first_memory) memories << ",";
          first_memory = false;
          memories << "{\"path_condition\":" << json_string(terms.from_expr(domain))
            << ",\"blocks\":" << observe_memory(memory, terms) << "}";
        }
      }
      memories << "]";
      node.returned_memories = memories.str();
      auto capture = [&](const Value &value) {
        const Value *source = &value;
        if (auto it = initialized.find(source); it != initialized.end()) source = it->second;
        if (auto saved = state.at(*source))
          node.values.push_back({value.getName(), value.getType().toString(),
            terms.from_expr(saved->val.value), terms.from_expr(saved->val.non_poison),
            terms.from_expr(saved->domain())});
      };
      for (auto &input : fn.getInputs()) capture(input);
      for (auto *global : fn.getGlobalVars()) capture(*global);
      for (auto &instruction : fn.instrs())
        if (instruction.getName().starts_with("%")) capture(instruction);
    };

    Node entry;
    entry.id = "n0";
    entry.snapshot_kind = "native_after_initialization";
    entry.function = fn_name;
    entry.block = "entry";
    entry.instr = "";
    entry.text = "entry";
    entry.state = "normal";
    entry.path = truth;
    entry.term = truth;
    entry.definedness = truth;
    entry.memory = observe_memory(state.getMemory(), terms);
    capture_values(entry);
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
        if (auto it = origin_definitions.find(instr.getName()); it != origin_definitions.end()) node.origin = it->second;
        else if (auto statement = origin_block_statements.find({bb->getName(), trim(printed.str())}); statement != origin_block_statements.end() && statement->second.size() == 1)
          node.origin = statement->second.front();
        else if (auto statement = origin_statements.find(trim(printed.str())); statement != origin_statements.end() && statement->second.size() == 1)
          node.origin = statement->second.front();
        node.unroll = unroll_index(bb->getName());
        node.path = terms.from_expr(state.getPath(*bb));
        node.definedness = terms.from_expr(val.domain());
        node.memory = observe_memory(state.getMemory(), terms);
        capture_values(node);
        node.term = terms.from_expr(val.val.value);
        if (val.domain().isFalse())
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
        if (auto *br = dynamic_cast<const Branch *>(&instr)) {
          auto remember = [&](const BasicBlock &dst, const char *kind) {
            auto guard = state.getJumpCond(*bb, dst);
            if (!guard.isFalse()) jumps.push_back({bb, &dst, kind, terms.from_expr(guard)});
          };
          remember(br->getTrue(), br->getCond() ? "taken" : "step");
          if (br->getFalse()) remember(*br->getFalse(), "not_taken");
        }
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

    for (auto &jump : jumps) {
      auto last = bb_last.find(jump.source->getName());
      if (last == bb_last.end()) continue;
      auto target = bb_first.find(jump.destination->getName());
      std::string target_id = target == bb_first.end() ? std::string() : target->second;
      if (jump.destination->getName() == "#sink") {
        Node sink;
        sink.id = "n" + std::to_string(nodes.size());
        sink.function = fn_name;
        sink.block = "#sink";
        sink.snapshot_kind = "native_predecessor_at_boundary";
        sink.text = "#sink";
        sink.unroll = unroll;
        sink.state = "bound_truncated";
        sink.path = jump.guard;
        sink.term = truth;
        sink.definedness = jump.guard;
        const auto &predecessor = nodes.at(std::stoul(last->second.substr(1)));
        sink.memory = predecessor.memory;
        sink.preconditions = predecessor.preconditions;
        sink.axioms = predecessor.axioms;
        sink.call_preconditions = predecessor.call_preconditions;
        sink.returned_values = predecessor.returned_values;
        sink.returned_memories = predecessor.returned_memories;
        sink.values = predecessor.values;
        target_id = sink.id;
        nodes.push_back(std::move(sink));
      }
      if (target_id.empty()) {
        assumptions.push_back("unobserved target " + jump.destination->getName());
        continue;
      }
      bool boundary = jump.destination->getName() == "#sink";
      saw_sink |= boundary;
      edges.push_back({"e" + std::to_string(edges.size()), last->second, target_id,
        boundary ? "boundary" : jump.kind, jump.guard, true});
    }
    std::map<std::string, unsigned> incoming_jumps;
    for (const auto &edge : edges) if (edge.native_jump) ++incoming_jumps[edge.to];
    for (auto &edge : edges)
      if (edge.native_jump && edge.kind == "step" && incoming_jumps[edge.to] > 1) edge.kind = "merge";

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

    TemporaryOutput temporary(graph_path);
    const auto &temporary_path = temporary.path;
    std::ofstream out(temporary_path);
    if (!out)
      throw std::runtime_error("cannot write " + graph_path);
    std::string ir_hash = sha256(program_text);
    std::string initial_hash = sha256(initial_text);
    out << "{\n";
    out << "  \"schema\": \"alive2-state-graph\",\n";
    out << "  \"schema_version\": 2,\n";
    out << "  \"fixture\": false,\n";
    out << "  \"run\": {\"id\": " << json_string("run-" + sha256(ir_hash + initial_hash + std::to_string(unroll) + ":" + std::to_string(budget_steps)).substr(0, 24))
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
    out << "], \"origin\": " << origin_json << "},\n";
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
    std::sort(terms.items.begin(), terms.items.end(), [](const Term &left, const Term &right) { return left.id < right.id; });
    for (size_t i = 0; i < terms.items.size(); ++i) {
      auto &term = terms.items[i];
      if (i)
        out << ", ";
      out << "{\"id\": " << json_string(term.id) << ", \"op\": " << json_string(term.op)
          << ", \"sort\": ";
      if (!term.sort_json.empty()) out << term.sort_json;
      else {
        out << "{\"kind\": " << json_string(term.sort);
        if (term.width >= 0) out << ", \"width\": " << term.width;
        out << "}";
      }
      out << ", \"parameters\": " << term.parameters;
      if (term.op == "unsupported") out << ", \"unsupported\": \"native AST kind, sort or declaration parameter not supported\"";
      if (!term.symbol.empty()) out << ", \"symbol\": " << json_string(term.symbol);
      out << ", \"args\": [";
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
    out << "  \"memories\": [";
    for (size_t i = 0; i < nodes.size(); ++i) {
      if (i) out << ", ";
      out << "{\"id\": " << json_string("mem" + std::to_string(i))
          << ", \"representation\": \"alive2-native-arrays\", \"blocks\": " << nodes[i].memory << ",\"returned\":" << nodes[i].returned_memories << "}";
    }
    out << "],\n";
    out << "  \"nodes\": [";
    for (size_t i = 0; i < nodes.size(); ++i) {
      auto &node = nodes[i];
      if (i)
        out << ", ";
      out << "{\"id\": " << json_string(node.id)
          << ", \"location\": {\"function\": " << json_string(node.function)
          << ", \"block\": " << json_string(node.block)
          << ", \"instr\": " << json_string(node.instr) << "}"
          << ", \"origin_location\": " << node.origin << ", \"unroll\": " << node.unroll
          << ", \"snapshot_kind\": " << json_string(node.snapshot_kind)
          << ", \"state\": " << json_string(node.state)
          << ", \"path_condition\": " << json_string(node.path)
          << ", \"ir_state\": {\"function\": " << json_string(node.function)
          << ", \"block\": " << json_string(node.block)
          << ", \"instr\": " << json_string(node.instr)
          << ", \"values\": [";
      for (size_t v = 0; v < node.values.size(); ++v) {
        if (v) out << ", ";
        const auto &binding = node.values[v];
        out << "{\"instr\": " << json_string(binding.name)
            << ", \"type\": " << json_string(binding.type)
            << ", \"term\": " << json_string(binding.term)
            << ", \"non_poison\": " << json_string(binding.non_poison)
            << ", \"definedness\": " << json_string(binding.domain) << "}";
      }
      out << "]"
          << ", \"returned_values\": " << node.returned_values
          << ", \"current_value\": " << json_string(node.term)
          << ", \"preconditions\": " << json_string(node.preconditions)
          << ", \"axioms\": " << json_string(node.axioms)
          << ", \"call_preconditions\": " << json_string(node.call_preconditions)
          << ", \"definedness\": " << json_string(node.definedness)
          << ", \"memory_id\": " << json_string("mem" + std::to_string(i)) << ", \"memory_status\": \"native_arrays\""
          << ", \"exec_status\": " << json_string(node.state) << "}"
          << ", \"rocq_ebpf\": null, \"rocq_mapping\": {\"status\":\"unsupported\",\"reason\":\"full source state embedding and independent Rocq checkpoint comparison are not implemented\"}, \"evidence_ids\": []";
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
          << ", \"ir_span\": [";
      const auto &source = nodes.at(std::stoul(edge.from.substr(1)));
      const auto &destination = nodes.at(std::stoul(edge.to.substr(1)));
      if (!source.instr.empty()) out << json_string(source.instr);
      if (!destination.instr.empty() && destination.instr != source.instr) {
        if (!source.instr.empty()) out << ",";
        out << json_string(destination.instr);
      }
      std::vector<std::string> changed;
      if (source.path != destination.path) changed.push_back("path_condition");
      if (source.definedness != destination.definedness) changed.push_back("ir_state.definedness");
      if (source.memory != destination.memory || source.returned_memories != destination.returned_memories) changed.push_back("ir_state.memory");
      if (source.returned_values != destination.returned_values) changed.push_back("ir_state.returned_values");
      for (const auto &binding : destination.values) {
        auto before = std::find_if(source.values.begin(), source.values.end(), [&](const auto &value) { return binding.name == value.name; });
        if (before == source.values.end() || before->term != binding.term || before->non_poison != binding.non_poison || before->domain != binding.domain)
          changed.push_back("ir_state.values." + binding.name);
      }
      out << "], \"guard_scope\": " << json_string(edge.native_jump ? "native_predecessor_path_and_ub" : "unconditional_step")
          << ", \"events\": [], \"events_status\":\"not_observed\", \"changed\": [";
      for (size_t c = 0; c < changed.size(); ++c) { if (c) out << ","; out << json_string(changed[c]); }
      out << "], \"evidence_ids\": []}";
    }
    out << "],\n  \"coverage\": {\"return_domain\": [";
    for (size_t i = 0; i < returns.size(); ++i) {
      if (i)
        out << ", ";
      out << json_string(returns[i]);
    }
    out << "], \"sink_domain\": [";
    bool first_sink = true;
    for (const auto &node : nodes) {
      if (node.state != "bound_truncated") continue;
      if (!first_sink) out << ", ";
      first_sink = false;
      out << json_string(node.id);
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
        << json_string(ir_hash) << "}],"
        << " \"note\": \"The C++ observer that walks State::exec is not a Rocq proof.\"}]\n";
    out << "}\n";

    out.close();
    if (!out) throw std::runtime_error("failed to write graph");
    std::filesystem::rename(temporary_path, graph_path);
    return 0;
  } catch (const std::exception &err) {
    std::cerr << err.what() << "\n";
    return 2;
  }
}
