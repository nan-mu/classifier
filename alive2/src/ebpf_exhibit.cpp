#include "ebpf.h"
#include "ebpf_concrete.h"
#include "ebpf_project.h"

#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace {

struct J {
  enum class Kind { Null, String, Number, Bool, Array, Object };
  Kind kind = Kind::Null;
  std::string text;
  bool flag = false;
  std::vector<J> array;
  std::vector<std::pair<std::string, J>> object;

  const J *find(const std::string &key) const {
    for (const auto &field : object) {
      if (field.first == key)
        return &field.second;
    }
    return nullptr;
  }

  const J &need(const std::string &key) const {
    const J *field = find(key);
    if (!field)
      throw std::runtime_error("json missing " + key);
    return *field;
  }
};

class JsonParser {
 public:
  explicit JsonParser(std::string text) : text(std::move(text)) {}

  J parse() {
    skip();
    J value = parse_value();
    skip();
    if (at != text.size())
      throw std::runtime_error("trailing json");
    return value;
  }

 private:
  std::string text;
  size_t at = 0;

  void skip() {
    while (at < text.size() && std::isspace(static_cast<unsigned char>(text[at])))
      ++at;
  }

  char peek() const {
    if (at >= text.size())
      throw std::runtime_error("truncated json");
    return text[at];
  }

  char get() {
    char c = peek();
    ++at;
    return c;
  }

  J parse_value() {
    skip();
    char c = peek();
    if (c == '{')
      return parse_object();
    if (c == '[')
      return parse_array();
    if (c == '"')
      return parse_string();
    if (c == 't' || c == 'f')
      return parse_bool();
    if (c == 'n')
      return parse_null();
    return parse_number();
  }

  J parse_object() {
    get();
    J value;
    value.kind = J::Kind::Object;
    skip();
    if (peek() == '}') {
      get();
      return value;
    }
    while (true) {
      skip();
      J key = parse_string();
      skip();
      if (get() != ':')
        throw std::runtime_error("json colon");
      value.object.emplace_back(key.text, parse_value());
      skip();
      char c = get();
      if (c == '}')
        return value;
      if (c != ',')
        throw std::runtime_error("json object");
    }
  }

  J parse_array() {
    get();
    J value;
    value.kind = J::Kind::Array;
    skip();
    if (peek() == ']') {
      get();
      return value;
    }
    while (true) {
      value.array.push_back(parse_value());
      skip();
      char c = get();
      if (c == ']')
        return value;
      if (c != ',')
        throw std::runtime_error("json array");
    }
  }

  J parse_string() {
    if (get() != '"')
      throw std::runtime_error("json string");
    J value;
    value.kind = J::Kind::String;
    while (true) {
      char c = get();
      if (c == '"')
        return value;
      if (c == '\\') {
        char esc = get();
        if (esc == 'n')
          value.text.push_back('\n');
        else if (esc == 'r')
          value.text.push_back('\r');
        else if (esc == 't')
          value.text.push_back('\t');
        else if (esc == 'u') {
          for (int i = 0; i < 4; ++i)
            get();
          value.text.push_back('?');
        } else {
          value.text.push_back(esc);
        }
      } else {
        value.text.push_back(c);
      }
    }
  }

  J parse_bool() {
    J value;
    value.kind = J::Kind::Bool;
    if (text.compare(at, 4, "true") == 0) {
      value.flag = true;
      at += 4;
      return value;
    }
    if (text.compare(at, 5, "false") == 0) {
      value.flag = false;
      at += 5;
      return value;
    }
    throw std::runtime_error("json bool");
  }

  J parse_null() {
    if (text.compare(at, 4, "null") != 0)
      throw std::runtime_error("json null");
    at += 4;
    return {};
  }

  J parse_number() {
    size_t start = at;
    if (peek() == '-')
      get();
    if (!std::isdigit(static_cast<unsigned char>(peek())))
      throw std::runtime_error("json number");
    while (at < text.size() && std::isdigit(static_cast<unsigned char>(text[at])))
      ++at;
    J value;
    value.kind = J::Kind::Number;
    value.text = text.substr(start, at - start);
    return value;
  }
};

std::string node_text(const J &node) {
  if (node.kind != J::Kind::Object)
    return "";
  const J *op = node.find("op");
  const J *cite = node.find("cite");
  const J *constant = node.find("constant");
  const J *var = node.find("var");
  const J *note = node.find("note");
  const J *partial = node.find("partial");
  std::string text = op ? op->text : std::string("?");
  if (var && !var->text.empty())
    text += " " + var->text;
  if (constant && !constant->text.empty())
    text += " " + constant->text;
  if (cite && !cite->text.empty())
    text += " [" + cite->text + "]";
  if (note && !note->text.empty())
    text += " (" + note->text + ")";
  if (partial && partial->flag)
    text += " partial";
  const J *children = node.find("children");
  if (children && children->kind == J::Kind::Array && !children->array.empty()) {
    text += "(";
    for (size_t i = 0; i < children->array.size(); ++i) {
      if (i)
        text += ", ";
      text += node_text(children->array[i]);
    }
    text += ")";
  }
  return text;
}

std::string render_markdown(const J &root) {
  std::ostringstream md;
  md << "# Exhibit\n\n";
  md << root.need("projection").text << "\n\n";
  md << "Run `alive2/exhibit/regen.sh` from the repository root.\n\n";
  md << "Each SMT cell is EQUIVALENT, COUNTEREXAMPLE, UNKNOWN, or UNSUPPORTED. "
        "UNKNOWN and UNSUPPORTED are not passes.\n\n";
  for (const auto &program : root.need("programs").array) {
    md << "## " << program.need("label").text << "\n\n";
    md << "Bytes `" << program.need("bytes").text << "`.\n\n";
    md << "Bug flag is " << program.need("bug").text << ".\n\n";
    if (program.need("loop").flag) {
      md << "The CFG has a back edge. The symbolic result is UNSUPPORTED. "
            "The program was not unrolled.\n\n";
    }
    for (const auto &pc : program.need("pcs").array) {
      md << "### pc " << pc.need("pc").text << " " << pc.need("insn").text << "\n\n";
      if (!pc.need("reason").text.empty())
        md << pc.need("reason").text << "\n\n";
      md << "Rules";
      const auto &rules = pc.need("rules").array;
      if (rules.empty())
        md << " are not recorded";
      for (size_t i = 0; i < rules.size(); ++i)
        md << (i ? ", " : " ") << "`" << rules[i].text << "`";
      md << ".\n\n";
      const auto &path = pc.need("path");
      md << "Symbolic path condition is " << path.need("verdict").text << ".\n\n";
      md << "Alive2 path is `" << node_text(path.need("alive")) << "`.\n\n";
      md << "Rocq projection path is `" << node_text(path.need("rocq")) << "`.\n\n";
      if (!path.need("smt").text.empty())
        md << "Alive2 smt path is `" << path.need("smt").text << "`.\n\n";
      if (!path.need("model").text.empty())
        md << "Path model is `" << path.need("model").text << "`.\n\n";
      auto table = [&](const char *title, const J &cells) {
        md << title << "\n\n";
        md << "| reg | alive tag | rocq tag | definedness | value |\n";
        md << "| --- | --- | --- | --- | --- |\n";
        for (const auto &cell : cells.array) {
          md << "| r" << cell.need("reg").text << " | " << cell.need("alive_tag").text
             << " | " << cell.need("rocq_tag").text << " | "
             << cell.need("definedness").text << " | " << cell.need("value").text
             << " |\n";
        }
        md << "\n";
        for (const auto &cell : cells.array) {
          if (cell.need("reg").text != "0")
            continue;
          md << "r0 Alive2 expression is `" << node_text(cell.need("alive")) << "`.\n\n";
          md << "r0 Rocq projection is `" << node_text(cell.need("rocq")) << "`.\n\n";
          if (!cell.need("smt").text.empty())
            md << "r0 Alive2 smt is `" << cell.need("smt").text << "`.\n\n";
          if (!cell.need("model").text.empty())
            md << "r0 model is `" << cell.need("model").text << "`.\n\n";
        }
      };
      table("Pre-state.", pc.need("pre"));
      table("Post-state.", pc.need("post"));
      md << "Successors.\n\n";
      const auto &edges = pc.need("edges").array;
      if (edges.empty())
        md << "This instruction has no successor edge.\n\n";
      for (const auto &edge : edges) {
        md << "Edge";
        if (edge.need("exit").flag)
          md << " to exit";
        else
          md << " to pc " << edge.need("target_pc").text << " block `"
             << edge.need("block").text << "`";
        md << " is " << edge.need("verdict").text << ".\n\n";
        md << "Alive2 jump condition is `" << node_text(edge.need("alive")) << "`.\n\n";
        md << "Rocq projection condition is `" << node_text(edge.need("rocq"))
           << "`.\n\n";
        if (!edge.need("smt").text.empty())
          md << "Alive2 smt condition is `" << edge.need("smt").text << "`.\n\n";
        if (!edge.need("model").text.empty())
          md << "Edge model is `" << edge.need("model").text << "`.\n\n";
      }
      const auto &phis = pc.need("phis").array;
      if (!phis.empty()) {
        md << "Phi inputs.\n\n";
        for (const auto &phi : phis) {
          md << "r" << phi.need("reg").text << " from `" << phi.need("pred").text
             << "` is " << phi.need("verdict").text << ".\n\n";
          md << "Alive2 incoming expression is `" << node_text(phi.need("alive"))
             << "`.\n\n";
          md << "Rocq projection arm is `" << node_text(phi.need("rocq")) << "`.\n\n";
          if (!phi.need("smt").text.empty())
            md << "Alive2 smt incoming is `" << phi.need("smt").text << "`.\n\n";
          if (!phi.need("model").text.empty())
            md << "Phi model is `" << phi.need("model").text << "`.\n\n";
        }
      }
    }
    const auto &cross = program.need("cross").array;
    if (!cross.empty()) {
      md << "Concrete cross-check of the projection against rocq-step. "
            "This is not the SMT result.\n\n";
      md << "| input | projection r0 | rocq-step r0 | match |\n";
      md << "| --- | --- | --- | --- |\n";
      for (const auto &row : cross) {
        md << "| " << row.need("label").text << " | " << row.need("projection").text
           << " | " << row.need("rocq").text << " | "
           << (row.need("match").flag ? "yes" : "no") << " |\n";
        if (!row.need("error").text.empty() && !row.need("match").flag)
          md << "\n" << row.need("label").text << " " << row.need("error").text << "\n";
      }
      md << "\n";
    }
  }
  md << "## Concrete sanity\n\n";
  md << "These edges are concrete traces. They are not the symbolic path condition.\n\n";
  const auto &concrete = root.need("concrete").array;
  if (concrete.empty()) {
    md << "No concrete trace was supplied. The symbolic successors above stay.\n\n";
  } else {
    for (const auto &row : concrete) {
      md << "### " << row.need("id").text << "\n\n";
      if (row.need("agree").flag)
        md << "The concrete traces agree.\n\n";
      else
        md << "Divergence is " << row.need("divergence").text << ".\n\n";
      for (const auto &step : row.need("steps").array) {
        md << "pc " << step.need("pc").text << " " << step.need("status").text
           << " to " << step.need("pc_after").text << ", r0 " << step.need("r0").text
           << ".\n\n";
      }
    }
  }
  return md.str();
}

std::vector<uint8_t> parse_hex(std::string_view hex) {
  std::string digits;
  for (char c : hex) {
    if (std::isspace(static_cast<unsigned char>(c)))
      continue;
    digits.push_back(c);
  }
  if (digits.size() % 2 != 0)
    throw std::runtime_error("odd hex length");
  std::vector<uint8_t> out;
  auto nyb = [](char c) -> int {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
  };
  for (size_t i = 0; i < digits.size(); i += 2) {
    int hi = nyb(digits[i]);
    int lo = nyb(digits[i + 1]);
    if (hi < 0 || lo < 0)
      throw std::runtime_error("bad hex");
    out.push_back(static_cast<uint8_t>((hi << 4) | lo));
  }
  return out;
}

std::vector<uint8_t> read_bytes(const std::filesystem::path &path) {
  std::ifstream in(path, std::ios::binary);
  if (!in)
    throw std::runtime_error("cannot read bytes");
  std::string text((std::istreambuf_iterator<char>(in)), {});
  bool hex = !text.empty();
  for (unsigned char c : text) {
    if (std::isspace(c))
      continue;
    if (!std::isxdigit(c))
      hex = false;
  }
  if (hex)
    return parse_hex(text);
  if (text.size() % 8 != 0)
    throw std::runtime_error("byte file is not a multiple of 8");
  return std::vector<uint8_t>(text.begin(), text.end());
}

uint64_t parse_u64(const std::string &text) {
  if (text.empty())
    throw std::runtime_error("empty input value");
  int base = 10;
  const char *body = text.c_str();
  if (text.size() > 2 && text[0] == '0' && (text[1] == 'x' || text[1] == 'X')) {
    base = 16;
    body += 2;
  }
  char *end = nullptr;
  unsigned long long value = std::strtoull(body, &end, base);
  if (!end || *end)
    throw std::runtime_error("bad input value");
  return static_cast<uint64_t>(value);
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
  if (const auto *idx = std::get_if<InsnPc>(&pc))
    return "pc" + std::to_string(idx->index);
  if (std::holds_alternative<ExitPc>(pc))
    return "exit";
  return "none";
}

std::string r0_text(const Obs &obs) {
  if (std::holds_alternative<std::monostate>(obs))
    return "UNDEF";
  if (const auto *bits = std::get_if<Bv64>(&obs)) {
    char buf[17];
    std::snprintf(buf, sizeof buf, "%016llx",
                  static_cast<unsigned long long>(bits->bits));
    return buf;
  }
  return "PTR";
}

std::vector<ConcreteRow> load_concrete(const std::filesystem::path &dir) {
  std::vector<ConcreteRow> rows;
  if (!std::filesystem::exists(dir))
    throw std::runtime_error("trace directory is missing");
  for (const auto &entry : std::filesystem::directory_iterator(dir)) {
    if (!entry.is_directory())
      continue;
    auto rocq_path = entry.path() / "rocq.trace.json";
    auto alive_path = entry.path() / "alive2.trace.json";
    if (!std::filesystem::exists(rocq_path) || !std::filesystem::exists(alive_path))
      continue;
    Trace rocq = read_trace(rocq_path);
    Trace alive = read_trace(alive_path);
    ConcreteRow row;
    row.id = rocq.case_id.empty() ? entry.path().filename().string() : rocq.case_id;
    auto found = first_divergence(rocq, alive);
    if (!found) {
      row.agree = true;
    } else if (!negative_holds(*found)) {
      throw std::runtime_error(row.id + " diverges outside the negative test");
    } else {
      row.agree = false;
      row.divergence = found->line;
    }
    for (const auto &step : rocq.steps) {
      ConcreteStepOut out;
      out.pc = step.pc.index;
      out.status = status_name(step.status);
      out.pc_after = pc_text(step.pc_after);
      out.r0 = r0_text(step.after.r[0]);
      row.steps.push_back(out);
    }
    rows.push_back(std::move(row));
  }
  return rows;
}

void write_file(const std::filesystem::path &path, const std::string &body) {
  std::filesystem::create_directories(path.parent_path());
  auto tmp = path;
  tmp += ".tmp";
  {
    std::ofstream file(tmp, std::ios::binary | std::ios::trunc);
    if (!file)
      throw std::runtime_error("cannot write " + path.string());
    file << body;
    file.flush();
    if (!file)
      throw std::runtime_error("cannot flush " + path.string());
  }
  if (std::rename(tmp.c_str(), path.c_str()) != 0)
    throw std::runtime_error("cannot replace " + path.string());
}

void usage() {
  std::cerr << "usage: ebpf-exhibit --check\n"
            << "       ebpf-exhibit [--traces DIR] [--json FILE] --out FILE\n"
            << "       ebpf-exhibit --bytes FILE [--in REG VALUE]... "
               "[--json FILE] --out FILE\n";
}

} // namespace

int main(int argc, char **argv) {
  bool check = false;
  std::string traces;
  std::string json_path;
  std::string out_path;
  std::string bytes_path;
  std::vector<std::pair<uint8_t, uint64_t>> bound;
  for (int i = 1; i < argc; ++i) {
    std::string arg = argv[i];
    if (arg == "--check")
      check = true;
    else if (arg == "--traces" && i + 1 < argc)
      traces = argv[++i];
    else if (arg == "--json" && i + 1 < argc)
      json_path = argv[++i];
    else if (arg == "--out" && i + 1 < argc)
      out_path = argv[++i];
    else if (arg == "--bytes" && i + 1 < argc)
      bytes_path = argv[++i];
    else if (arg == "--in" && i + 2 < argc) {
      int reg = std::atoi(argv[++i]);
      if (reg < 0 || reg > 9) {
        usage();
        return 2;
      }
      bound.emplace_back(static_cast<uint8_t>(reg), parse_u64(argv[++i]));
    } else {
      usage();
      return 2;
    }
  }
  if (check)
    return symbolic_check();
  if (out_path.empty()) {
    usage();
    return 2;
  }
  try {
    ExhibitDoc doc;
    if (bytes_path.empty()) {
      doc = analyze_default();
    } else {
      auto code = read_bytes(bytes_path);
      std::vector<std::pair<uint8_t, std::string>> inputs;
      for (auto [reg, bits] : bound) {
        (void)bits;
        inputs.emplace_back(reg, "r" + std::to_string(reg));
      }
      doc.projection =
          "The Rocq side is a projection of the vendored instruction rules. "
          "It is not native Rocq symbolic execution. "
          "EQUIVALENT means the inequality is unsat under the assumption that each named input is not undef and not poison. "
          "An undef register can have definedness EQUIVALENT and value UNSUPPORTED. "
          "That UNSUPPORTED cell is not a pass.";
      doc.programs.push_back(analyze_bytes(code, inputs, bound, LiftBug::None, "bytes"));
    }
    if (!traces.empty())
      doc.concrete = load_concrete(traces);
    std::string json = exhibit_json(doc);
    if (!json_path.empty())
      write_file(json_path, json);
    J parsed = JsonParser(json).parse();
    write_file(out_path, render_markdown(parsed));
  } catch (const std::exception &ex) {
    std::cerr << ex.what() << "\n";
    return 1;
  }
  return 0;
}
