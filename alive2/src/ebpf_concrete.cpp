#include "ebpf_concrete.h"

#include <CommonCrypto/CommonDigest.h>

#include <cctype>
#include <cerrno>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <unistd.h>
#include <sys/wait.h>

namespace {

std::string hex16(uint64_t bits) {
  char buf[17];
  std::snprintf(buf, sizeof buf, "%016llx",
                static_cast<unsigned long long>(bits));
  return buf;
}

std::string status_name(StepStatus status) {
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

StepStatus status_of(std::string_view name) {
  if (name == "NEXT") return StepStatus::Next;
  if (name == "EXIT") return StepStatus::Exit;
  if (name == "STUCK") return StepStatus::Stuck;
  if (name == "UB") return StepStatus::Ub;
  if (name == "INCOMPLETE") return StepStatus::Incomplete;
  if (name == "UNSUPPORTED") return StepStatus::Unsupported;
  throw std::runtime_error("unknown status");
}

const char *role_name(PtrRole role) {
  switch (role) {
  case PtrRole::Code: return "code";
  case PtrRole::Stack: return "stack";
  case PtrRole::Ctx: return "ctx";
  case PtrRole::Other: return "other";
  }
  return "other";
}

PtrRole role_of(std::string_view name) {
  if (name == "code") return PtrRole::Code;
  if (name == "stack") return PtrRole::Stack;
  if (name == "ctx") return PtrRole::Ctx;
  if (name == "other") return PtrRole::Other;
  throw std::runtime_error("unknown pointer role");
}

std::string sha256_hex(const uint8_t *data, size_t n) {
  unsigned char dig[CC_SHA256_DIGEST_LENGTH];
  CC_SHA256(data, static_cast<CC_LONG>(n), dig);
  static const char *kHex = "0123456789abcdef";
  std::string out(CC_SHA256_DIGEST_LENGTH * 2, '0');
  for (size_t i = 0; i < CC_SHA256_DIGEST_LENGTH; ++i) {
    out[i * 2] = kHex[dig[i] >> 4];
    out[i * 2 + 1] = kHex[dig[i] & 0xf];
  }
  return out;
}

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

uint64_t parse_hex64(std::string_view hex) {
  if (hex.empty() || hex.size() > 16)
    throw std::runtime_error("bad bit hex");
  uint64_t v = 0;
  for (char c : hex) {
    int n = (c >= '0' && c <= '9') ? c - '0'
            : (c >= 'a' && c <= 'f') ? c - 'a' + 10
            : (c >= 'A' && c <= 'F') ? c - 'A' + 10
                                     : -1;
    if (n < 0)
      throw std::runtime_error("bad bit hex");
    v = (v << 4) | static_cast<uint64_t>(n);
  }
  return v;
}

std::string json_escape(std::string_view s) {
  std::string out;
  for (char c : s) {
    if (c == '\\' || c == '"') {
      out.push_back('\\');
      out.push_back(c);
    } else {
      out.push_back(c);
    }
  }
  return out;
}

void write_obs(std::ostream &o, const Obs &obs, int indent) {
  auto pad = std::string(indent, ' ');
  if (std::holds_alternative<std::monostate>(obs)) {
    o << "{\n" << pad << "  \"tag\": \"UNDEF\"\n" << pad << "}";
    return;
  }
  if (auto *bits = std::get_if<Bv64>(&obs)) {
    o << "{\n" << pad << "  \"tag\": \"BV64\",\n" << pad
      << "  \"hex\": \"" << hex16(bits->bits) << "\"\n" << pad << "}";
    return;
  }
  const auto &ptr = std::get<Ptr>(obs);
  o << "{\n" << pad << "  \"tag\": \"PTR\",\n" << pad << "  \"role\": \""
    << role_name(ptr.role) << "\",\n" << pad << "  \"hex\": \""
    << hex16(ptr.offset) << "\"\n" << pad << "}";
}

void write_regs(std::ostream &o, const RegFile &regs, int indent) {
  auto pad = std::string(indent, ' ');
  o << "{\n";
  for (int i = 0; i < 10; ++i) {
    o << pad << "  \"r" << i << "\": ";
    write_obs(o, regs.r[i], indent + 2);
    if (i + 1 != 10)
      o << ",";
    o << "\n";
  }
  o << pad << "}";
}

std::string trace_json(const Trace &trace) {
  std::ostringstream o;
  o << "{\n";
  o << "  \"case_id\": \"" << json_escape(trace.case_id) << "\",\n";
  o << "  \"bytes_hex\": \"" << json_escape(trace.bytes_hex) << "\",\n";
  o << "  \"bytes_sha256\": \"" << json_escape(trace.bytes_sha256) << "\",\n";
  o << "  \"inputs\": [\n";
  for (size_t i = 0; i < trace.inputs.size(); ++i) {
    o << "    {\"reg\": " << static_cast<int>(trace.inputs[i].first)
      << ", \"hex\": \"" << hex16(trace.inputs[i].second.bits) << "\"}";
    if (i + 1 != trace.inputs.size())
      o << ",";
    o << "\n";
  }
  o << "  ],\n";
  o << "  \"bug\": \""
    << (trace.bug == BugFlag::DivZeroAsUb ? "div-zero-as-ub" : "none")
    << "\",\n";
  o << "  \"exclusions\": [\"undef-either-side\", \"no-r10\", \"no-rax\", "
       "\"memory-empty-only\"],\n";
  o << "  \"memory\": \""
    << (trace.memory == MemorySummary::Changed ? "changed" : "empty")
    << "\",\n";
  o << "  \"producer\": \""
    << (trace.producer == Producer::Failed ? "failed" : "ok") << "\",\n";
  o << "  \"steps\": [\n";
  for (size_t i = 0; i < trace.steps.size(); ++i) {
    const auto &s = trace.steps[i];
    o << "    {\n";
    o << "      \"pc\": " << s.pc.index << ",\n";
    o << "      \"pc_after\": ";
    if (auto *idx = std::get_if<InsnPc>(&s.pc_after))
      o << idx->index;
    else if (std::holds_alternative<ExitPc>(s.pc_after))
      o << "\"exit\"";
    else
      o << "null";
    o << ",\n";
    o << "      \"source_hex\": \"" << json_escape(s.source_hex) << "\",\n";
    o << "      \"status\": \"" << status_name(s.status) << "\",\n";
    o << "      \"before\": ";
    write_regs(o, s.before, 6);
    o << ",\n";
    o << "      \"after\": ";
    write_regs(o, s.after, 6);
    o << ",\n";
    o << "      \"return_value\": ";
    if (s.return_value)
      o << "\"" << hex16(s.return_value->bits) << "\"";
    else
      o << "null";
    o << "\n    }";
    if (i + 1 != trace.steps.size())
      o << ",";
    o << "\n";
  }
  o << "  ]\n}\n";
  return o.str();
}

struct Json {
  enum Kind { Null, String, Number, Bool, Array, Object } kind = Null;
  std::string str;
  int64_t num = 0;
  bool b = false;
  std::vector<Json> arr;
  std::vector<std::pair<std::string, Json>> obj;

  const Json *field(std::string_view key) const {
    for (const auto &kv : obj)
      if (kv.first == key)
        return &kv.second;
    return nullptr;
  }
  const Json &need(std::string_view key) const {
    const Json *f = field(key);
    if (!f)
      throw std::runtime_error(std::string("missing ") + std::string(key));
    return *f;
  }
};

class Cursor {
 public:
  explicit Cursor(std::string_view in) : in(in) {}

  Json parse() {
    Json v = value();
    skip();
    if (i != in.size())
      throw std::runtime_error("trailing json");
    return v;
  }

 private:
  std::string_view in;
  size_t i = 0;

  void skip() {
    while (i < in.size() && std::isspace(static_cast<unsigned char>(in[i])))
      ++i;
  }

  char get() {
    if (i >= in.size())
      throw std::runtime_error("truncated json");
    return in[i++];
  }

  Json value() {
    skip();
    if (i >= in.size())
      throw std::runtime_error("truncated json");
    char c = in[i];
    if (c == '{') return object();
    if (c == '[') return array();
    if (c == '"') return string();
    if (c == 'n') return literal("null", Json::Null);
    if (c == 't') return literal("true", Json::Bool, true);
    if (c == 'f') return literal("false", Json::Bool, false);
    return number();
  }

  Json literal(const char *word, Json::Kind kind, bool b = false) {
    for (const char *p = word; *p; ++p) {
      if (get() != *p)
        throw std::runtime_error("bad json literal");
    }
    Json j;
    j.kind = kind;
    j.b = b;
    return j;
  }

  Json string() {
    skip();
    if (get() != '"')
      throw std::runtime_error("expected string");
    std::string s;
    while (true) {
      char c = get();
      if (c == '"')
        break;
      if (c == '\\') {
        char e = get();
        if (e != '\\' && e != '"')
          throw std::runtime_error("bad json escape");
        s.push_back(e);
      } else {
        s.push_back(c);
      }
    }
    Json j;
    j.kind = Json::String;
    j.str = std::move(s);
    return j;
  }

  Json number() {
    skip();
    size_t start = i;
    if (i < in.size() && in[i] == '-')
      ++i;
    if (i >= in.size() || !std::isdigit(static_cast<unsigned char>(in[i])))
      throw std::runtime_error("expected number");
    while (i < in.size() && std::isdigit(static_cast<unsigned char>(in[i])))
      ++i;
    Json j;
    j.kind = Json::Number;
    j.num = std::stoll(std::string(in.substr(start, i - start)));
    return j;
  }

  Json array() {
    if (get() != '[')
      throw std::runtime_error("expected array");
    Json j;
    j.kind = Json::Array;
    skip();
    if (i < in.size() && in[i] == ']') {
      ++i;
      return j;
    }
    while (true) {
      j.arr.push_back(value());
      skip();
      char c = get();
      if (c == ']')
        break;
      if (c != ',')
        throw std::runtime_error("expected comma");
    }
    return j;
  }

  Json object() {
    if (get() != '{')
      throw std::runtime_error("expected object");
    Json j;
    j.kind = Json::Object;
    skip();
    if (i < in.size() && in[i] == '}') {
      ++i;
      return j;
    }
    while (true) {
      Json key = string();
      skip();
      if (get() != ':')
        throw std::runtime_error("expected colon");
      j.obj.emplace_back(key.str, value());
      skip();
      char c = get();
      if (c == '}')
        break;
      if (c != ',')
        throw std::runtime_error("expected comma");
    }
    return j;
  }
};

Obs obs_of(const Json &j) {
  if (j.kind != Json::Object)
    throw std::runtime_error("register is not an object");
  const auto &tag = j.need("tag");
  if (tag.kind != Json::String)
    throw std::runtime_error("register tag");
  if (tag.str == "UNDEF")
    return std::monostate{};
  if (tag.str == "BV64")
    return Bv64{parse_hex64(j.need("hex").str)};
  if (tag.str == "PTR")
    return Ptr{role_of(j.need("role").str), parse_hex64(j.need("hex").str)};
  throw std::runtime_error("bad register tag");
}

RegFile regs_of(const Json &j) {
  if (j.kind != Json::Object)
    throw std::runtime_error("register file");
  RegFile regs;
  for (int i = 0; i < 10; ++i) {
    std::string key = "r" + std::to_string(i);
    regs.r[i] = obs_of(j.need(key));
  }
  if (j.field("r10") || j.field("rax"))
    throw std::runtime_error("r10 or rax in a trace");
  return regs;
}

Step step_of(const Json &j, std::string_view bytes) {
  Step s;
  if (j.need("pc").kind != Json::Number || j.need("pc").num < 0)
    throw std::runtime_error("bad pc");
  s.pc.index = static_cast<uint32_t>(j.need("pc").num);
  const auto &after = j.need("pc_after");
  if (after.kind == Json::Null)
    s.pc_after = std::monostate{};
  else if (after.kind == Json::String) {
    if (after.str != "exit")
      throw std::runtime_error("bad pc_after");
    s.pc_after = ExitPc{};
  } else if (after.kind == Json::Number) {
    if (after.num < 0)
      throw std::runtime_error("bad pc_after");
    s.pc_after = InsnPc{static_cast<uint32_t>(after.num)};
  } else {
    throw std::runtime_error("bad pc_after");
  }
  s.source_hex = j.need("source_hex").str;
  if (s.source_hex != word_at(bytes, s.pc))
    throw std::runtime_error("source_hex does not match the program bytes");
  s.status = status_of(j.need("status").str);
  s.before = regs_of(j.need("before"));
  s.after = regs_of(j.need("after"));
  const auto &ret = j.need("return_value");
  if (ret.kind == Json::Null)
    s.return_value = std::nullopt;
  else if (ret.kind == Json::String)
    s.return_value = Bv64{parse_hex64(ret.str)};
  else
    throw std::runtime_error("bad return_value");
  return s;
}

bool exact_obs(const Obs &a, const Obs &b) {
  if (a.index() != b.index())
    return false;
  if (auto *x = std::get_if<Bv64>(&a))
    return x->bits == std::get<Bv64>(b).bits;
  if (auto *x = std::get_if<Ptr>(&a)) {
    const auto &y = std::get<Ptr>(b);
    return x->role == y.role && x->offset == y.offset;
  }
  return true;
}

bool same_obs(const Obs &a, const Obs &b) { return exact_obs(a, b); }

bool comparable(const Obs &a, const Obs &b) {
  if (std::holds_alternative<std::monostate>(a) ||
      std::holds_alternative<std::monostate>(b))
    return false;
  return true;
}

std::string obs_text(const Obs &o) {
  if (std::holds_alternative<std::monostate>(o))
    return "UNDEF";
  if (auto *b = std::get_if<Bv64>(&o))
    return hex16(b->bits);
  const auto &p = std::get<Ptr>(o);
  return std::string("PTR ") + role_name(p.role) + " " + hex16(p.offset);
}

std::string pc_after_text(const PcAfter &pc) {
  if (auto *idx = std::get_if<InsnPc>(&pc))
    return std::to_string(idx->index);
  if (std::holds_alternative<ExitPc>(pc))
    return "exit";
  return "none";
}

bool same_pc_after(const PcAfter &a, const PcAfter &b) {
  if (a.index() != b.index())
    return false;
  if (auto *x = std::get_if<InsnPc>(&a))
    return x->index == std::get<InsnPc>(b).index;
  return true;
}

std::string capture(const std::string &exe, const std::vector<std::string> &args,
                    const std::string &input, int &code) {
  int in_pipe[2];
  int out_pipe[2];
  if (pipe(in_pipe) != 0 || pipe(out_pipe) != 0)
    throw std::runtime_error("pipe");
  pid_t pid = fork();
  if (pid < 0)
    throw std::runtime_error("fork");
  if (pid == 0) {
    dup2(in_pipe[0], STDIN_FILENO);
    dup2(out_pipe[1], STDOUT_FILENO);
    close(in_pipe[0]);
    close(in_pipe[1]);
    close(out_pipe[0]);
    close(out_pipe[1]);
    std::vector<char *> argv;
    argv.push_back(const_cast<char *>(exe.c_str()));
    for (const auto &arg : args)
      argv.push_back(const_cast<char *>(arg.c_str()));
    argv.push_back(nullptr);
    execv(exe.c_str(), argv.data());
    _exit(127);
  }
  close(in_pipe[0]);
  close(out_pipe[1]);
  size_t off = 0;
  while (off < input.size()) {
    ssize_t n = write(in_pipe[1], input.data() + off, input.size() - off);
    if (n < 0) {
      if (errno == EINTR)
        continue;
      break;
    }
    off += static_cast<size_t>(n);
  }
  close(in_pipe[1]);
  std::string out;
  char buf[4096];
  while (true) {
    ssize_t n = read(out_pipe[0], buf, sizeof buf);
    if (n < 0) {
      if (errno == EINTR)
        continue;
      break;
    }
    if (n == 0)
      break;
    out.append(buf, static_cast<size_t>(n));
  }
  close(out_pipe[0]);
  int status = 0;
  waitpid(pid, &status, 0);
  code = WIFEXITED(status) ? WEXITSTATUS(status) : 127;
  return out;
}

std::optional<uint64_t> exit_bits(const Trace &trace) {
  for (const auto &step : trace.steps) {
    if (step.status == StepStatus::Exit && step.return_value)
      return step.return_value->bits;
  }
  return std::nullopt;
}

bool traces_equal(const Trace &a, const Trace &b) {
  if (a.case_id != b.case_id || a.bytes_hex != b.bytes_hex ||
      a.bytes_sha256 != b.bytes_sha256 || a.bug != b.bug ||
      a.memory != b.memory || a.producer != b.producer ||
      a.inputs.size() != b.inputs.size() || a.steps.size() != b.steps.size())
    return false;
  for (size_t i = 0; i < a.inputs.size(); ++i) {
    if (a.inputs[i].first != b.inputs[i].first ||
        a.inputs[i].second.bits != b.inputs[i].second.bits)
      return false;
  }
  for (size_t i = 0; i < a.steps.size(); ++i) {
    const auto &x = a.steps[i];
    const auto &y = b.steps[i];
    if (x.pc.index != y.pc.index || x.status != y.status ||
        x.source_hex != y.source_hex || !same_pc_after(x.pc_after, y.pc_after))
      return false;
    if (x.return_value.has_value() != y.return_value.has_value())
      return false;
    if (x.return_value && x.return_value->bits != y.return_value->bits)
      return false;
    for (int r = 0; r < 10; ++r) {
      if (!exact_obs(x.before.r[r], y.before.r[r]) ||
          !exact_obs(x.after.r[r], y.after.r[r]))
        return false;
    }
  }
  return true;
}

}

const std::vector<Fixture> &kFixtures() {
  static const std::vector<Fixture> rows = {
      {"div64-7-2", "bf100000000000003f200000000000009500000000000000",
       {{1, 7}, {2, 2}}, BugFlag::None, false, 3},
      {"div64-7-0", "bf100000000000003f200000000000009500000000000000",
       {{1, 7}, {2, 0}}, BugFlag::None, false, 0},
      {"sdiv64-min--1", "bf100000000000003f200100000000009500000000000000",
       {{1, 0x8000000000000000ull}, {2, 0xffffffffffffffffull}}, BugFlag::None,
       false, 0x8000000000000000ull},
      {"jgt64-11",
       "bf10000000000000250002000a0000001700000001000000050001000000000007000000"
       "010000009500000000000000",
       {{1, 11}}, BugFlag::None, false, 12},
      {"jgt64-10",
       "bf10000000000000250002000a0000001700000001000000050001000000000007000000"
       "010000009500000000000000",
       {{1, 10}}, BugFlag::None, false, 9},
      {"div64-7-0-div-zero-as-ub",
       "bf100000000000003f200000000000009500000000000000",
       {{1, 7}, {2, 0}}, BugFlag::DivZeroAsUb, true, 0},
  };
  return rows;
}

std::string word_at(std::string_view bytes_hex, InsnPc pc) {
  size_t at = static_cast<size_t>(pc.index) * 16;
  if (at + 16 > bytes_hex.size())
    throw std::runtime_error("pc outside the program bytes");
  return std::string(bytes_hex.substr(at, 16));
}

Trace stamp(const Fixture &fixture, Trace trace) {
  auto bytes = parse_hex(fixture.bytes_hex);
  trace.case_id = fixture.id;
  trace.bytes_hex = fixture.bytes_hex;
  trace.bytes_sha256 = sha256_hex(bytes.data(), bytes.size());
  trace.inputs.clear();
  for (auto [reg, bits] : fixture.inputs)
    trace.inputs.emplace_back(reg, Bv64{bits});
  trace.bug = fixture.bug;
  trace.exclusions = {Exclusion::UndefEitherSide, Exclusion::NoR10,
                      Exclusion::NoRax, Exclusion::MemoryEmptyOnly};
  for (auto &step : trace.steps)
    step.source_hex = word_at(trace.bytes_hex, step.pc);
  return trace;
}

Trace parse_rocq_stream(std::string_view stdout_bytes) {
  Trace trace;
  std::string pending(stdout_bytes);
  std::vector<std::string> lines;
  std::string cur;
  for (char c : pending) {
    if (c == '\n') {
      lines.push_back(cur);
      cur.clear();
    } else {
      cur.push_back(c);
    }
  }
  if (!cur.empty())
    lines.push_back(cur);
  if (lines.empty() || lines.back() != "end")
    throw std::runtime_error("rocq stream does not end with end");
  size_t n = 0;
  auto take = [&]() -> const std::string & {
    if (n >= lines.size())
      throw std::runtime_error("truncated rocq stream");
    return lines[n++];
  };
  if (take() != "contract NEXT EXIT STUCK INCOMPLETE")
    throw std::runtime_error("rocq contract line");
  const auto &memory = take();
  if (memory == "memory empty")
    trace.memory = MemorySummary::Empty;
  else if (memory == "memory changed")
    trace.memory = MemorySummary::Changed;
  else
    throw std::runtime_error("rocq memory line");
  while (true) {
    const auto &mark = take();
    if (mark == "end")
      break;
    if (mark != "step")
      throw std::runtime_error("expected step");
    Step step;
    const auto &pc = take();
    if (pc.rfind("pc ", 0) != 0)
      throw std::runtime_error("expected pc");
    step.pc.index = static_cast<uint32_t>(std::stoul(pc.substr(3)));
    const auto &status = take();
    if (status.rfind("status ", 0) != 0)
      throw std::runtime_error("expected status");
    auto name = status.substr(7);
    if (name == "UB" || name == "UNSUPPORTED")
      throw std::runtime_error("rocq stream carries a non-rocq status");
    step.status = status_of(name);
    const auto &after = take();
    if (after == "pc_after exit") {
      if (step.status != StepStatus::Exit)
        throw std::runtime_error("exit pc on a non-exit step");
      step.pc_after = ExitPc{};
    } else if (after == "pc_after none") {
      step.pc_after = std::monostate{};
    } else if (after.rfind("pc_after ", 0) == 0) {
      if (step.status == StepStatus::Exit)
        throw std::runtime_error("numeric exit pc");
      step.pc_after = InsnPc{static_cast<uint32_t>(std::stoul(after.substr(9)))};
    } else {
      throw std::runtime_error("expected pc_after");
    }
    const auto &ret = take();
    if (ret == "return none")
      step.return_value = std::nullopt;
    else if (ret.rfind("return ", 0) == 0)
      step.return_value = Bv64{parse_hex64(ret.substr(7))};
    else
      throw std::runtime_error("expected return");
    auto load_regs = [&](RegFile &regs) {
      for (int i = 0; i < 10; ++i) {
        const auto &row = take();
        std::string key = "r" + std::to_string(i) + " ";
        if (row.rfind(key, 0) != 0)
          throw std::runtime_error("register out of order");
        if (row.find("r10") != std::string::npos ||
            row.find("rax") != std::string::npos)
          throw std::runtime_error("r10 or rax in the rocq stream");
        auto body = row.substr(key.size());
        if (body == "UNDEF")
          regs.r[i] = std::monostate{};
        else if (body == "UNSUPPORTED")
          throw std::runtime_error("unsupported rocq value");
        else if (body.rfind("BV64 ", 0) == 0)
          regs.r[i] = Bv64{parse_hex64(body.substr(5))};
        else if (body.rfind("PTR ", 0) == 0) {
          std::istringstream iss(body.substr(4));
          std::string role;
          std::string hex;
          iss >> role >> hex;
          regs.r[i] = Ptr{role_of(role), parse_hex64(hex)};
        } else {
          throw std::runtime_error("bad register value");
        }
      }
    };
    if (take() != "before")
      throw std::runtime_error("expected before");
    load_regs(step.before);
    if (take() != "after")
      throw std::runtime_error("expected after");
    load_regs(step.after);
    if (take() != "endstep")
      throw std::runtime_error("expected endstep");
    trace.steps.push_back(std::move(step));
  }
  if (n != lines.size())
    throw std::runtime_error("rocq stream has trailing lines");
  trace.producer = Producer::Ok;
  return trace;
}

std::optional<Divergence> first_divergence(const Trace &rocq, const Trace &alive) {
  auto header = [](std::string line) {
    Divergence d;
    d.kind = DivergenceKind::Header;
    d.line = std::move(line);
    return d;
  };
  if (rocq.case_id != alive.case_id || rocq.bytes_hex != alive.bytes_hex ||
      rocq.bytes_sha256 != alive.bytes_sha256 || rocq.bug != alive.bug ||
      rocq.inputs.size() != alive.inputs.size())
    return header("header");
  for (size_t i = 0; i < rocq.inputs.size(); ++i) {
    if (rocq.inputs[i].first != alive.inputs[i].first ||
        rocq.inputs[i].second.bits != alive.inputs[i].second.bits)
      return header("header inputs");
  }
  if (rocq.exclusions != alive.exclusions) {
    Divergence d;
    d.kind = DivergenceKind::Exclusion;
    d.line = "exclusion";
    return d;
  }
  if (rocq.producer != Producer::Ok || alive.producer != Producer::Ok) {
    Divergence d;
    d.kind = DivergenceKind::Producer;
    d.line = "producer alive2=" +
             std::string(alive.producer == Producer::Ok ? "ok" : "failed") +
             " rocq=" +
             std::string(rocq.producer == Producer::Ok ? "ok" : "failed");
    return d;
  }
  if (rocq.memory != MemorySummary::Empty ||
      alive.memory != MemorySummary::Empty) {
    Divergence d;
    d.kind = DivergenceKind::Memory;
    d.line = "memory alive2=" +
             std::string(alive.memory == MemorySummary::Empty ? "empty"
                                                              : "changed") +
             " rocq=" +
             std::string(rocq.memory == MemorySummary::Empty ? "empty"
                                                             : "changed");
    return d;
  }
  size_t n = std::min(rocq.steps.size(), alive.steps.size());
  for (size_t i = 0; i < n; ++i) {
    const auto &r = rocq.steps[i];
    const auto &a = alive.steps[i];
    auto at = [&](DivergenceKind kind, std::string line) {
      Divergence d;
      d.kind = kind;
      d.step = static_cast<int>(i);
      d.pc = r.pc.index;
      d.line = std::move(line);
      return d;
    };
    if (r.pc.index != a.pc.index)
      return at(DivergenceKind::Pc,
                "pc alive2=" + std::to_string(a.pc.index) +
                    " rocq=" + std::to_string(r.pc.index));
    if (r.source_hex != a.source_hex)
      return at(DivergenceKind::Source,
                "pc " + std::to_string(r.pc.index) + " source alive2=" +
                    a.source_hex + " rocq=" + r.source_hex);
    if (r.status != a.status)
      return at(DivergenceKind::Status,
                "pc " + std::to_string(r.pc.index) + " status alive2=" +
                    status_name(a.status) + " rocq=" + status_name(r.status));
    auto ret_text = [](const std::optional<Bv64> &v) {
      return v ? hex16(v->bits) : std::string("none");
    };
    if (ret_text(r.return_value) != ret_text(a.return_value))
      return at(DivergenceKind::ReturnValue,
                "pc " + std::to_string(r.pc.index) + " return alive2=" +
                    ret_text(a.return_value) + " rocq=" +
                    ret_text(r.return_value));
    if (!same_pc_after(r.pc_after, a.pc_after))
      return at(DivergenceKind::PcAfter,
                "pc " + std::to_string(r.pc.index) + " pc_after alive2=" +
                    pc_after_text(a.pc_after) + " rocq=" +
                    pc_after_text(r.pc_after));
    for (int reg = 0; reg < 10; ++reg) {
      if (!comparable(r.after.r[reg], a.after.r[reg]))
        continue;
      if (!same_obs(r.after.r[reg], a.after.r[reg]))
        return at(DivergenceKind::Reg,
                  "pc " + std::to_string(r.pc.index) + " reg r" +
                      std::to_string(reg) + " alive2=" +
                      obs_text(a.after.r[reg]) + " rocq=" +
                      obs_text(r.after.r[reg]));
    }
  }
  if (rocq.steps.size() != alive.steps.size()) {
    Divergence d;
    d.kind = DivergenceKind::StepCount;
    d.line = "steps alive2=" + std::to_string(alive.steps.size()) +
             " rocq=" + std::to_string(rocq.steps.size());
    return d;
  }
  return std::nullopt;
}

bool negative_holds(const Divergence &found) {
  return found.line == "pc 1 status alive2=UB rocq=NEXT";
}

void write_trace(const std::filesystem::path &path, const Trace &trace) {
  std::filesystem::create_directories(path.parent_path());
  auto tmp = path;
  tmp += ".tmp";
  {
    std::ofstream out(tmp, std::ios::binary | std::ios::trunc);
    if (!out)
      throw std::runtime_error("cannot write trace");
    out << trace_json(trace);
    out.flush();
    if (!out)
      throw std::runtime_error("cannot flush trace");
  }
  if (std::rename(tmp.c_str(), path.c_str()) != 0)
    throw std::runtime_error("cannot replace trace");
}

Trace read_trace(const std::filesystem::path &path) {
  std::ifstream in(path);
  if (!in)
    throw std::runtime_error("cannot read trace");
  std::ostringstream buf;
  buf << in.rdbuf();
  Json root = Cursor(buf.str()).parse();
  Trace trace;
  trace.case_id = root.need("case_id").str;
  trace.bytes_hex = root.need("bytes_hex").str;
  trace.bytes_sha256 = root.need("bytes_sha256").str;
  auto bytes = parse_hex(trace.bytes_hex);
  if (trace.bytes_sha256 != sha256_hex(bytes.data(), bytes.size()))
    throw std::runtime_error("bytes_sha256 does not match bytes_hex");
  const auto &inputs = root.need("inputs");
  if (inputs.kind != Json::Array)
    throw std::runtime_error("inputs");
  for (const auto &row : inputs.arr) {
    if (row.need("reg").num < 0 || row.need("reg").num > 9)
      throw std::runtime_error("input register");
    trace.inputs.emplace_back(static_cast<uint8_t>(row.need("reg").num),
                              Bv64{parse_hex64(row.need("hex").str)});
  }
  auto bug = root.need("bug").str;
  if (bug == "none")
    trace.bug = BugFlag::None;
  else if (bug == "div-zero-as-ub")
    trace.bug = BugFlag::DivZeroAsUb;
  else
    throw std::runtime_error("bug");
  const auto &ex = root.need("exclusions");
  if (ex.kind != Json::Array || ex.arr.size() != 4 ||
      ex.arr[0].str != "undef-either-side" || ex.arr[1].str != "no-r10" ||
      ex.arr[2].str != "no-rax" || ex.arr[3].str != "memory-empty-only")
    throw std::runtime_error("exclusions");
  auto memory = root.need("memory").str;
  if (memory == "empty")
    trace.memory = MemorySummary::Empty;
  else if (memory == "changed")
    trace.memory = MemorySummary::Changed;
  else
    throw std::runtime_error("memory");
  auto producer = root.need("producer").str;
  if (producer == "ok")
    trace.producer = Producer::Ok;
  else if (producer == "failed")
    trace.producer = Producer::Failed;
  else
    throw std::runtime_error("producer");
  const auto &steps = root.need("steps");
  if (steps.kind != Json::Array)
    throw std::runtime_error("steps");
  for (const auto &step : steps.arr)
    trace.steps.push_back(step_of(step, trace.bytes_hex));
  return trace;
}

namespace {

std::string request_of(const Fixture &fixture) {
  std::ostringstream req;
  req << "bytes " << fixture.bytes_hex << "\n";
  for (auto [reg, bits] : fixture.inputs)
    req << "in " << static_cast<int>(reg) << " " << hex16(bits) << "\n";
  return req.str();
}

std::string trim(std::string s) {
  while (!s.empty() && (s.back() == '\n' || s.back() == '\r'))
    s.pop_back();
  return s;
}

bool head_matches(std::string &why) {
  std::ifstream pin(PIN_PATH);
  std::string want;
  std::getline(pin, want);
  constexpr const char *kSemanticsCommit =
      "78d65a77592aae84b31f86385f8be4ab83b45ccb";
  if (want != kSemanticsCommit) {
    why = "PIN is not " + std::string(kSemanticsCommit);
    return false;
  }
  if (!std::filesystem::exists(std::filesystem::path(SEMANTICS_DIR) / ".git")) {
    // Vendored sources have no checkout. The digest is the pin.
  } else {
    int code = 0;
    auto got = trim(capture("/usr/bin/git",
                            {"-C", SEMANTICS_DIR, "rev-parse", "HEAD"}, "", code));
    if (code != 0 || got != want) {
      why = "semantics HEAD is " + got + ", PIN is " + want;
      return false;
    }
  }
  std::ifstream dig(SOURCES_SHA_PATH);
  std::string want_dig;
  std::getline(dig, want_dig);
  if (want_dig.size() != 64) {
    why = "SOURCES.sha256 is missing";
    return false;
  }
  int dcode = 0;
  auto raw = trim(capture(
      "/bin/sh",
      {"-c", std::string("cd ") + SEMANTICS_DIR +
                 " && find theories validator -name '*.v' -print | sort | "
                 "xargs shasum -a 256 | shasum -a 256"},
      "", dcode));
  auto got_dig = raw.substr(0, raw.find(' '));
  if (dcode != 0 || got_dig != want_dig) {
    why = "semantics sources hash is " + got_dig + ", SOURCES.sha256 is " +
          want_dig;
    return false;
  }
  return true;
}

bool contract_ok() {
  int code = 0;
  auto out = capture(ROCQ_STEP, {"--contract"}, "", code);
  return code == 0 && out.rfind("contract NEXT EXIT STUCK INCOMPLETE\n", 0) == 0 &&
         out.size() >= 4 && out.substr(out.size() - 4) == "end\n";
}

struct Row {
  bool ok = false;
  bool sanity = false;
  std::optional<Divergence> found;
};

Row run_row(const Fixture &fixture, const std::filesystem::path &dir) {
  Row row;
  Trace rocq;
  rocq.producer = Producer::Failed;
  try {
    int code = 0;
    auto out = capture(ROCQ_STEP, {}, request_of(fixture), code);
    if (code != 0)
      throw std::runtime_error("rocq-step failed");
    rocq = parse_rocq_stream(out);
  } catch (const std::exception &) {
    rocq.producer = Producer::Failed;
  }
  Trace alive;
  alive.producer = Producer::Failed;
  try {
    std::vector<std::pair<uint8_t, Bv64>> inputs;
    for (auto [reg, bits] : fixture.inputs)
      inputs.emplace_back(reg, Bv64{bits});
    alive = alive2_trace(parse_hex(fixture.bytes_hex), inputs, fixture.bug);
    alive.producer = Producer::Ok;
  } catch (const std::exception &) {
    alive.producer = Producer::Failed;
  }
  rocq = stamp(fixture, std::move(rocq));
  alive = stamp(fixture, std::move(alive));
  auto rocq_path = dir / fixture.id / "rocq.trace.json";
  auto alive_path = dir / fixture.id / "alive2.trace.json";
  write_trace(rocq_path, rocq);
  write_trace(alive_path, alive);
  bool roundtrip = false;
  try {
    roundtrip = traces_equal(rocq, read_trace(rocq_path)) &&
                traces_equal(alive, read_trace(alive_path));
  } catch (const std::exception &) {
    roundtrip = false;
  }
  row.found = first_divergence(rocq, alive);
  if (!roundtrip && !row.found) {
    Divergence d;
    d.kind = DivergenceKind::Header;
    d.line = "roundtrip";
    row.found = d;
  }
  auto got = exit_bits(rocq);
  row.sanity = fixture.sanity_r0 && got && *got == *fixture.sanity_r0;
  if (fixture.must_fail_div_zero)
    row.ok = row.found && negative_holds(*row.found) && row.sanity && roundtrip;
  else
    row.ok = !row.found && row.sanity && roundtrip;
  return row;
}

}

int main(int argc, char **argv) {
  std::string out;
  std::optional<std::string> only;
  for (int i = 1; i < argc; ++i) {
    std::string arg = argv[i];
    if (arg == "--out" && i + 1 < argc)
      out = argv[++i];
    else if (arg == "--only" && i + 1 < argc)
      only = argv[++i];
    else {
      std::cerr << "usage: ebpf-concrete --out DIR [--only ID]\n";
      return 2;
    }
  }
  if (out.empty()) {
    std::cerr << "usage: ebpf-concrete --out DIR [--only ID]\n";
    return 2;
  }
  std::string why;
  if (!head_matches(why)) {
    std::cerr << why << "\n";
    return 2;
  }
  if (!contract_ok()) {
    std::cerr << "rocq-step contract mismatch\n";
    return 2;
  }
  bool saw = false;
  bool suite = true;
  for (const auto &fixture : kFixtures()) {
    if (only && *only != fixture.id)
      continue;
    saw = true;
    Row row = run_row(fixture, out);
    std::cout << fixture.id << " comparator=" << (row.found ? "FAIL" : "PASS")
              << " sanity=" << (row.sanity ? "ok" : "bad") << "\n";
    if (row.found)
      std::cout << "  " << row.found->line << "\n";
    if (!row.ok)
      suite = false;
  }
  if (!saw) {
    std::cerr << "unknown fixture\n";
    return 2;
  }
  std::cout << "suite=" << (suite ? "PASS" : "FAIL") << "\n";
  return suite ? 0 : 1;
}
