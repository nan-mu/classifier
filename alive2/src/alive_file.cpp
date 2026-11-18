#include "alive_file.h"
#include "ir/constant.h"
#include "ir/function.h"
#include "ir/instr.h"
#include "ir/globals.h"
#include "ir/state.h"
#include "smt/smt.h"
#include "util/symexec.h"

#include <bit>
#include <cctype>
#include <fstream>
#include <iostream>
#include <map>
#include <memory>
#include <sstream>
#include <set>
#include <limits>
#include <string>
#include <vector>

using namespace IR;

namespace {

struct Types {
  IntType i64{"i64", 64};
  IntType i32{"i32", 32};
  IntType i16{"i16", 16};
  IntType i8{"i8", 8};
  IntType i1{"i1", 1};
  PtrType ptr{"ptr"};

  Type &of(const std::string &name) {
    if (name == "i64") return i64;
    if (name == "i32") return i32;
    if (name == "i16") return i16;
    if (name == "i8") return i8;
    if (name == "i1") return i1;
    if (name == "ptr") return ptr;
    throw std::runtime_error("unknown type " + name);
  }
};

struct Prog {
  Types types;
  std::unique_ptr<Function> fn;
  std::map<std::string, Value *> vals;
  std::map<std::string, BasicBlock *> blocks;
  BasicBlock *cur = nullptr;
  std::vector<std::tuple<Phi *, std::string, std::string>> phis;

  explicit Prog() = default;

  Value &imm(Type &ty, const std::string &text) {
    auto key = ty.toString() + " " + text;
    if (auto it = vals.find(key); it != vals.end())
      return *it->second;
    if (!ty.isIntType())
      throw std::runtime_error("integer literal with non-integer type");
    size_t used = 0;
    int64_t n = std::stoll(text, &used);
    if (used != text.size())
      throw std::runtime_error("invalid integer literal " + text);
    if (ty.bits() < 64) {
      auto bits = ty.bits();
      if (n < -(int64_t(1) << (bits - 1)) || n > (int64_t(1) << bits) - 1)
        throw std::runtime_error("integer literal outside type range");
    }
    auto c = std::make_unique<IntConst>(ty, n);
    Value &ref = *c;
    vals.emplace(key, &ref);
    fn->addConstant(std::move(c));
    return ref;
  }

  Value &use(const std::string &ty, const std::string &tok) {
    if (!tok.empty() && (tok[0] == '%' || tok[0] == '@')) {
      auto it = vals.find(tok);
      if (it == vals.end())
        throw std::runtime_error("undefined value " + tok);
      if (it->second->getType().toString() != ty)
        throw std::runtime_error("type mismatch for " + tok + ": expected " + ty);
      return *it->second;
    }
    return imm(types.of(ty), tok);
  }

  void def(const std::string &name, Value &val) {
    if (!vals.emplace(name, &val).second)
      throw std::runtime_error("duplicate definition " + name);
  }
};

std::vector<std::string> tokens(const std::string &line) {
  std::vector<std::string> out;
  std::string cur;
  for (char c : line) {
    if (std::isspace(static_cast<unsigned char>(c)) || c == ',' || c == '(' || c == ')' || c == '{' || c == '}') {
      if (!cur.empty()) {
        out.push_back(cur);
        cur.clear();
      }
    } else {
      cur.push_back(c);
    }
  }
  if (!cur.empty())
    out.push_back(cur);
  return out;
}

[[noreturn]] void bad(int line, const std::string &why) {
  throw std::runtime_error("line " + std::to_string(line) + ": " + why);
}

BinOp::Op binop(const std::string &op) {
  if (op == "add") return BinOp::Add;
  if (op == "sub") return BinOp::Sub;
  if (op == "mul") return BinOp::Mul;
  if (op == "udiv") return BinOp::UDiv;
  if (op == "sdiv") return BinOp::SDiv;
  if (op == "urem") return BinOp::URem;
  if (op == "srem") return BinOp::SRem;
  if (op == "shl") return BinOp::Shl;
  if (op == "lshr") return BinOp::LShr;
  if (op == "ashr") return BinOp::AShr;
  if (op == "and") return BinOp::And;
  if (op == "or") return BinOp::Or;
  if (op == "xor") return BinOp::Xor;
  throw std::runtime_error("unknown binop " + op);
}

ICmp::Cond icmp(const std::string &op) {
  if (op == "eq") return ICmp::EQ;
  if (op == "ne") return ICmp::NE;
  if (op == "ugt") return ICmp::UGT;
  if (op == "uge") return ICmp::UGE;
  if (op == "ult") return ICmp::ULT;
  if (op == "ule") return ICmp::ULE;
  if (op == "sgt") return ICmp::SGT;
  if (op == "sge") return ICmp::SGE;
  if (op == "slt") return ICmp::SLT;
  if (op == "sle") return ICmp::SLE;
  throw std::runtime_error("unknown icmp " + op);
}

bool is_type(const std::string &name) {
  return name == "i64" || name == "i32" || name == "i16" || name == "i8" || name == "i1" || name == "ptr";
}

MemoryAccess::AccessType access_type(std::string loc) {
  if (!loc.empty() && loc.back() == ':')
    loc.pop_back();
  if (loc == "argmem") return MemoryAccess::Args;
  if (loc == "globals") return MemoryAccess::Globals;
  if (loc == "inaccessiblemem") return MemoryAccess::Inaccessible;
  if (loc == "errno") return MemoryAccess::Errno;
  if (loc == "other") return MemoryAccess::Other;
  throw std::runtime_error("unknown memory location " + loc);
}

MemoryAccess parse_memory(const std::vector<std::string> &tok, size_t at) {
  if (at >= tok.size() || tok[at] != "memory")
    throw std::runtime_error("missing memory attribute");
  if (at + 1 >= tok.size())
    throw std::runtime_error("truncated memory attribute");
  MemoryAccess mem;
  const std::string &first = tok[at + 1];
  if (first == "none" || first == "read" || first == "write") {
    if (at + 2 != tok.size())
      throw std::runtime_error("malformed memory attribute");
    if (first == "none") mem.setNoAccess();
    else if (first == "read") mem.setCanOnlyRead();
    else mem.setCanOnlyWrite();
    return mem;
  }
  for (size_t i = at + 1; i < tok.size(); i += 2) {
    if (i + 1 >= tok.size())
      throw std::runtime_error("truncated memory attribute");
    if (tok[i].empty() || tok[i].back() != ':')
      throw std::runtime_error("unknown memory attribute " + tok[i]);
    auto ty = access_type(tok[i]);
    const std::string &mode = tok[i + 1];
    if (mode == "read") mem.setCanAlsoRead(ty);
    else if (mode == "write") mem.setCanAlsoWrite(ty);
    else if (mode == "readwrite") mem.setCanAlsoAccess(ty);
    else throw std::runtime_error("unknown memory mode " + mode);
  }
  return mem;
}

size_t memory_at(const std::vector<std::string> &tok) {
  for (size_t i = 0; i < tok.size(); ++i)
    if (tok[i] == "memory")
      return i;
  throw std::runtime_error("missing memory attribute");
}

void parse_define(Prog &p, const std::vector<std::string> &tok) {
  if (tok.size() < 3 || tok[0] != "define" || tok[2].empty() || tok[2][0] != '@')
    throw std::runtime_error("malformed define");
  size_t mem = memory_at(tok);
  if (p.fn)
    throw std::runtime_error("multiple function definitions");
  p.fn = std::make_unique<Function>(p.types.of(tok[1]), std::string(tok[2].substr(1)));
  p.fn->getFnAttrs().mem = parse_memory(tok, mem);
  if ((mem - 3) % 2)
    throw std::runtime_error("malformed function inputs");
  for (size_t i = 3; i + 1 < mem; i += 2) {
    if (!is_type(tok[i]) || tok[i + 1].empty() || tok[i + 1][0] != '%')
      throw std::runtime_error("malformed function input");
    auto in = std::make_unique<Input>(p.types.of(tok[i]), std::string(tok[i + 1]));
    p.def(tok[i + 1], *in);
    p.fn->addInput(std::move(in));
  }
}

void parse_declare(Prog &p, const std::vector<std::string> &tok) {
  if (!p.fn)
    throw std::runtime_error("declare before define");
  if (tok.size() < 3 || tok[2].empty())
    throw std::runtime_error("malformed declare");
  Function::FnDecl decl;
  decl.name = tok[2][0] == '@' ? tok[2].substr(1) : tok[2];
  decl.output = &p.types.of(tok[1]);
  size_t mem = memory_at(tok);
  for (size_t i = 3; i < mem; ++i) {
    if (tok[i] == "...") {
      decl.is_varargs = true;
      continue;
    }
    if (!is_type(tok[i]))
      throw std::runtime_error("unknown declare token " + tok[i]);
    decl.inputs.emplace_back(&p.types.of(tok[i]), ParamAttrs());
  }
  decl.attrs.mem = parse_memory(tok, mem);
  for (const auto &other : p.fn->getFnDecls())
    if (other.name == decl.name) throw std::runtime_error("duplicate declaration " + decl.name);
  p.fn->addFnDecl(std::move(decl));
}

void one_insn(Prog &p, int lineno, const std::vector<std::string> &t) {
  if (t.empty())
    return;
  auto need = [&](size_t n) {
    if (t.size() < n)
      bad(lineno, "truncated instruction");
  };
  auto exact = [&](size_t n) {
    need(n);
    if (t.size() != n)
      bad(lineno, "unexpected instruction tokens");
  };
  auto require = [&](bool ok, const char *why) {
    if (!ok) bad(lineno, why);
  };
  auto alignment = [&](const std::string &text) {
    size_t used = 0;
    auto n = std::stoull(text, &used);
    require(used == text.size() && n && !(n & (n - 1)) && text[0] != '-', "invalid alignment");
    return n;
  };
  if (p.cur->size() && (dynamic_cast<const Branch *>(&p.cur->back()) || dynamic_cast<const Return *>(&p.cur->back())))
    bad(lineno, "instruction after terminator");
  if (t[0] == "br") {
    if (t.size() >= 3 && t[1].starts_with("i")) {
      exact(7);
      require(t[1] == "i1" && t[3] == "label" && t[5] == "label", "malformed conditional branch");
      auto &cond = p.use(t[1], t[2]);
      auto *yes = p.blocks.at(t[4]);
      auto *no = p.blocks.at(t[6]);
      p.cur->addInstr(std::make_unique<Branch>(cond, *yes, *no));
    } else {
      exact(3);
      require(t[1] == "label", "malformed branch");
      p.cur->addInstr(std::make_unique<Branch>(*p.blocks.at(t[2])));
    }
    return;
  }
  if (t[0] == "ret") {
    exact(3);
    require(t[1] == p.fn->getType().toString(), "return type mismatch");
    p.cur->addInstr(std::make_unique<Return>(p.types.of(t[1]), p.use(t[1], t[2])));
    return;
  }
  if (t[0] == "store") {
    exact(7);
    require(t[3] == "ptr" && t[5] == "align", "malformed store");
    auto &val = p.use(t[1], t[2]);
    auto &ptr = p.use(t[3], t[4]);
    uint64_t align = alignment(t[6]);
    p.cur->addInstr(std::make_unique<Store>(ptr, val, align));
    return;
  }
  need(3);
  if (t[1] != "=")
    bad(lineno, "expected assignment");
  const std::string &name = t[0];
  require(name.starts_with("%") && name.size() > 1, "malformed SSA name");
  const std::string &op = t[2];
  if (op == "alloca") {
    exact(7);
    require(t[3] == "i64" && t[5] == "align", "malformed alloca");
    auto &sz = p.use(t[3], t[4]);
    uint64_t align = alignment(t[6]);
    auto insn = std::make_unique<Alloc>(p.types.ptr, std::string(name), sz, nullptr, align);
    p.def(name, *insn);
    p.cur->addInstr(std::move(insn));
  } else if (op == "gep") {
    need(9);
    require(t[3] == "ptr" && (t.size() - 5) % 4 == 0, "malformed gep");
    auto &base = p.use(t[3], t[4]);
    auto gep = std::make_unique<GEP>(p.types.ptr, std::string(name), base, false, false, false);
    size_t i = 5;
    while (i + 3 < t.size()) {
      require(t[i + 1] == "x" && t[i + 2] == "i64", "malformed gep index");
      size_t used = 0;
      uint64_t scale = std::stoull(t[i], &used);
      require(used == t[i].size() && t[i][0] != '-', "invalid gep scale");
      auto &idx = p.use(t[i + 2], t[i + 3]);
      gep->addIdx(scale, idx);
      i += 4;
    }
    p.def(name, *gep);
    p.cur->addInstr(std::move(gep));
  } else if (op == "load") {
    exact(8);
    require(t[4] == "ptr" && t[6] == "align", "malformed load");
    auto &ptr = p.use(t[4], t[5]);
    uint64_t align = alignment(t[7]);
    auto insn = std::make_unique<Load>(p.types.of(t[3]), std::string(name), ptr, align);
    p.def(name, *insn);
    p.cur->addInstr(std::move(insn));
  } else if (op == "zext" || op == "sext" || op == "trunc" || op == "ptrtoint" || op == "inttoptr") {
    exact(7);
    require(t[5] == "to", "malformed conversion");
    auto &from = p.types.of(t[3]);
    auto &to = p.types.of(t[6]);
    if (op == "ptrtoint") require(t[3] == "ptr" && to.isIntType(), "invalid ptrtoint types");
    else if (op == "inttoptr") require(from.isIntType() && t[6] == "ptr", "invalid inttoptr types");
    else {
      require(from.isIntType() && to.isIntType(), "invalid integer conversion types");
      require(op == "trunc" ? from.bits() > to.bits() : from.bits() < to.bits(), "invalid conversion widths");
    }
    auto kind = op == "zext" ? ConversionOp::ZExt : op == "sext" ? ConversionOp::SExt
               : op == "trunc" ? ConversionOp::Trunc : op == "ptrtoint" ? ConversionOp::Ptr2Int
               : ConversionOp::Int2Ptr;
    auto &src = p.use(t[3], t[4]);
    auto insn = std::make_unique<ConversionOp>(p.types.of(t[6]), std::string(name), src, kind);
    p.def(name, *insn);
    p.cur->addInstr(std::move(insn));
  } else if (op == "icmp") {
    exact(7);
    require(p.types.of(t[4]).isIntType(), "icmp requires integer operands");
    auto &a = p.use(t[4], t[5]);
    auto &b = p.use(t[4], t[6]);
    auto insn = std::make_unique<ICmp>(p.types.i1, std::string(name), icmp(t[3]), a, b);
    p.def(name, *insn);
    p.cur->addInstr(std::move(insn));
  } else if (op == "phi") {
    need(8);
    require((t.size() - 4) % 4 == 0, "malformed phi");
    auto phi = std::make_unique<Phi>(p.types.of(t[3]), std::string(name));
    Phi *raw = phi.get();
    p.def(name, *phi);
    p.cur->addInstr(std::move(phi));
    for (size_t i = 4; i + 3 < t.size(); i += 4) {
      if (t[i] != "[" || t[i + 3] != "]")
        bad(lineno, "malformed phi");
      p.phis.emplace_back(raw, t[i + 1], t[i + 2]);
    }
  } else if (op == "call") {
    need(5);
    size_t end = t.size();
    for (size_t i = 5; i < t.size(); ++i) if (t[i] == "memory") { end = i; break; }
    require((end - 5) % 2 == 0 && !t[4].empty(), "malformed call");
    std::string callee = t[4];
    if (!callee.empty() && callee[0] == '@')
      callee = callee.substr(1);
    const Function::FnDecl *decl = nullptr;
    for (const auto &candidate : p.fn->getFnDecls())
      if (candidate.name == callee) decl = &candidate;
    require(decl && !decl->is_varargs, "missing or unsupported call declaration");
    require(decl->output->toString() == t[3] && decl->inputs.size() == (end - 5) / 2, "call signature mismatch");
    for (size_t i = 5; i + 1 < end; i += 2)
      require(decl->inputs[(i - 5) / 2].first->toString() == t[i], "call argument type mismatch");
    auto attrs = decl->attrs;
    if (end != t.size()) require(parse_memory(t, end) == attrs.mem, "call memory attribute differs from declaration");
    auto call = std::make_unique<FnCall>(p.types.of(t[3]), std::string(name), std::move(callee), std::move(attrs));
    for (size_t i = 5; i + 1 < end; i += 2)
      call->addArg(p.use(t[i], t[i + 1]), ParamAttrs());
    p.def(name, *call);
    p.cur->addInstr(std::move(call));
  } else {
    try {
      binop(op);
    } catch (const std::runtime_error &) {
      bad(lineno, "unknown opcode " + op);
    }
    exact(6);
    require(p.types.of(t[3]).isIntType(), "binary operation requires integer operands");
    auto &a = p.use(t[3], t[4]);
    auto &b = p.use(t[3], t[5]);
    auto insn = std::make_unique<BinOp>(p.types.of(t[3]), std::string(name), a, b, binop(op));
    p.def(name, *insn);
    p.cur->addInstr(std::move(insn));
  }
}

const char *ALIVE_FILE = "; alive-file v1";
const char *ALIVE2_PIN = "; alive2-pin adacbd5180ccf95075e9867c4f0c259f59c9fef2";
const char *ROCQ_PIN = "; rocq-pin 78d65a77592aae84b31f86385f8be4ab83b45ccb";

std::string trim(const std::string &text) {
  auto begin = text.find_first_not_of(" \t\r");
  if (begin == std::string::npos)
    return "";
  auto end = text.find_last_not_of(" \t\r");
  return text.substr(begin, end - begin + 1);
}

void note_header(const std::string &line, bool &file, bool &alive, bool &rocq) {
  if (line.starts_with("; alive-file")) {
    if (line != ALIVE_FILE)
      throw std::runtime_error("unsupported alive-file version");
    file = true;
  } else if (line.starts_with("; alive2-pin")) {
    if (line != ALIVE2_PIN)
      throw std::runtime_error("unsupported alive2 pin");
    alive = true;
  } else if (line.starts_with("; rocq-pin")) {
    if (line != ROCQ_PIN)
      throw std::runtime_error("unsupported rocq pin");
    rocq = true;
  }
}

void load_text(Prog &p, const std::string &text) {
  std::stringstream in(text);
  std::string line;
  std::vector<std::pair<int, std::string>> body;
  int lineno = 0;
  bool saw_file = false, saw_alive = false, saw_rocq = false;
  bool opened = false, closed = false;
  while (std::getline(in, line)) {
    ++lineno;
    auto trimmed = trim(line);
    if (trimmed.starts_with(";")) {
      if (!body.empty() && (trimmed.starts_with("; alive-file") || trimmed.starts_with("; alive2-pin") || trimmed.starts_with("; rocq-pin"))) bad(lineno, "header must precede declarations and definition");
      note_header(trimmed, saw_file, saw_alive, saw_rocq);
      continue;
    }
    auto cut = trimmed.find(';');
    if (cut != std::string::npos) {
      note_header(trim(trimmed.substr(cut)), saw_file, saw_alive, saw_rocq);
      trimmed = trim(trimmed.substr(0, cut));
    }
    if (trimmed.empty()) continue;
    if (!saw_file || !saw_alive || !saw_rocq) bad(lineno, "missing alive-file header or pin before body");
    if (closed) bad(lineno, "content after function closing brace");
    if (trimmed.starts_with("define ")) {
      if (opened) bad(lineno, "multiple function definitions");
      if (!trimmed.ends_with("{")) bad(lineno, "missing function opening brace");
      opened = true;
    }
    if (trimmed == "}") {
      if (!opened) bad(lineno, "closing brace before function");
      closed = true;
      continue;
    }
    body.emplace_back(lineno, trimmed);
  }
  if (!saw_file || !saw_alive || !saw_rocq)
    throw std::runtime_error("missing alive-file v1 header or pin");
  if (!opened || !closed) throw std::runtime_error("missing function definition or closing brace");
  bool in_fn = false;
  std::vector<std::vector<std::string>> pending_decl;
  for (auto &[no, line] : body) {
    auto t = tokens(line);
    if (t.empty())
      continue;
    if (t[0] == "declare") {
      if (p.fn)
        parse_declare(p, t);
      else
        pending_decl.push_back(std::move(t));
      continue;
    }
    if (t[0] == "define") {
      parse_define(p, t);
      for (auto &decl : pending_decl)
        parse_declare(p, decl);
      pending_decl.clear();
      in_fn = true;
      continue;
    }
    if (!in_fn)
      bad(no, "instruction before define");
    if (line.back() == ':') {
      auto label = "%" + line.substr(0, line.size() - 1);
      auto &bb = p.fn->getBB(label);
      if (!p.blocks.emplace(label, &bb).second)
        bad(no, "duplicate block " + label);
    }
  }
  if (p.blocks.empty())
    throw std::runtime_error("function has no block");
  for (auto &[no, line] : body) {
    auto t = tokens(line);
    if (t.empty() || t[0] == "declare" || t[0] == "define")
      continue;
    if (line.back() == ':') {
      p.cur = p.blocks.at("%" + line.substr(0, line.size() - 1));
      continue;
    }
    if (!p.cur)
      bad(no, "instruction before a block label");
    try {
      one_insn(p, no, t);
    } catch (const std::out_of_range &) {
      bad(no, "unknown block or value");
    } catch (const std::exception &err) {
      if (std::string(err.what()).starts_with("line "))
        throw;
      bad(no, err.what());
    }
  }
  for (auto &[phi, val, bb] : p.phis) {
    auto it = p.vals.find(val);
    if (it == p.vals.end()) {
      if (val.empty() || val[0] == '%')
        throw std::runtime_error("phi uses undefined value " + val);
      phi->addValue(p.imm(p.types.of(phi->getType().toString()), val), std::string(bb));
    } else {
      if (it->second->getType().toString() != phi->getType().toString())
        throw std::runtime_error("phi type mismatch");
      phi->addValue(*it->second, std::string(bb));
    }
  }
  std::map<std::string, std::set<std::string>> predecessors;
  for (auto *bb : p.fn->getBBs()) {
    if (bb->size() == 0 || (!dynamic_cast<const Branch *>(&bb->back()) && !dynamic_cast<const Return *>(&bb->back())))
      throw std::runtime_error("block " + bb->getName() + " does not end in br or ret");
    if (auto *br = dynamic_cast<const Branch *>(&bb->back())) {
      predecessors[br->getTrue().getName()].insert(bb->getName());
      if (br->getFalse()) predecessors[br->getFalse()->getName()].insert(bb->getName());
    }
  }
  for (auto *bb : p.fn->getBBs()) {
    bool saw_non_phi = false;
    for (size_t i = 0; i < bb->size(); ++i) {
      auto *phi = dynamic_cast<const Phi *>(&bb->at(i));
      if (!phi) { saw_non_phi = true; continue; }
      if (saw_non_phi) throw std::runtime_error("phi after non-phi instruction");
      std::set<std::string> sources;
      for (const auto &[value, source] : phi->getValues())
        if (!sources.insert(source).second) throw std::runtime_error("duplicate phi predecessor");
      if (sources != predecessors[bb->getName()])
        throw std::runtime_error("phi predecessors do not match block predecessors");
    }
  }
  std::set<const BasicBlock *> reachable;
  std::vector<const BasicBlock *> pending{p.fn->getBBs().front()};
  while (!pending.empty()) {
    auto *bb = pending.back(); pending.pop_back();
    if (!reachable.insert(bb).second) continue;
    if (auto *br = dynamic_cast<const Branch *>(&bb->back())) {
      pending.push_back(&br->getTrue());
      if (br->getFalse()) pending.push_back(br->getFalse());
    }
  }
  if (reachable.size() != p.blocks.size()) throw std::runtime_error("unreachable blocks are unsupported");
  if (!predecessors[p.fn->getBBs().front()->getName()].empty()) throw std::runtime_error("entry block has predecessors");
  p.fn->topSort();
  CFG cfg(*p.fn);
  DomTree dominators(*p.fn, cfg);
  std::map<const Value *, std::pair<const BasicBlock *, size_t>> definitions;
  for (auto *bb : p.fn->getBBs())
    for (size_t i = 0; i < bb->size(); ++i) definitions.emplace(&bb->at(i), std::pair(bb, i));
  auto check_use = [&](const Value *value, const BasicBlock *bb, size_t position) {
    auto def = definitions.find(value);
    if (def == definitions.end()) return;
    auto [source, index] = def->second;
    if (source == bb ? index >= position : !dominators.dominates(source, bb))
      throw std::runtime_error("value " + value->getName() + " does not dominate its use");
  };
  for (auto *bb : p.fn->getBBs()) {
    for (size_t i = 0; i < bb->size(); ++i) {
      const auto &instruction = bb->at(i);
      if (auto *phi = dynamic_cast<const Phi *>(&instruction)) {
        for (auto &[value, predecessor] : phi->getValues()) {
          const auto *source = p.blocks.at(predecessor);
          check_use(value, source, source->size() - 1);
        }
      } else {
        for (auto *operand : instruction.operands()) check_use(operand, bb, i);
      }
    }
  }
}

const char *binop_name(BinOp::Op op) {
  switch (op) {
  case BinOp::Add: return "add";
  case BinOp::Sub: return "sub";
  case BinOp::Mul: return "mul";
  case BinOp::SDiv: return "sdiv";
  case BinOp::UDiv: return "udiv";
  case BinOp::SRem: return "srem";
  case BinOp::URem: return "urem";
  case BinOp::Shl: return "shl";
  case BinOp::AShr: return "ashr";
  case BinOp::LShr: return "lshr";
  case BinOp::And: return "and";
  case BinOp::Or: return "or";
  case BinOp::Xor: return "xor";
  default: return "binop";
  }
}

const char *conv_name(ConversionOp::Op op) {
  switch (op) {
  case ConversionOp::SExt: return "sext";
  case ConversionOp::ZExt: return "zext";
  case ConversionOp::Trunc: return "trunc";
  case ConversionOp::Ptr2Int: return "ptrtoint";
  case ConversionOp::Int2Ptr: return "inttoptr";
  default: return "conv";
  }
}

std::string value_desc(Value &value) {
  if (auto *constant = dynamic_cast<IntConst *>(&value)) {
    if (auto number = constant->getInt())
      return "imm:" + value.getType().toString() + ":" + std::to_string(*number);
  }
  return value.getName() + ":" + value.getType().toString();
}

std::string kind_of(const Instr &insn) {
  if (auto *op = dynamic_cast<const BinOp *>(&insn)) return binop_name(op->getOp());
  if (auto *op = dynamic_cast<const ConversionOp *>(&insn)) return conv_name(op->getOp());
  if (dynamic_cast<const ICmp *>(&insn)) return "icmp";
  if (dynamic_cast<const Phi *>(&insn)) return "phi";
  if (dynamic_cast<const Branch *>(&insn)) return "br";
  if (dynamic_cast<const Return *>(&insn)) return "ret";
  if (dynamic_cast<const Load *>(&insn)) return "load";
  if (dynamic_cast<const Store *>(&insn)) return "store";
  if (dynamic_cast<const GEP *>(&insn)) return "gep";
  if (dynamic_cast<const Alloc *>(&insn)) return "alloca";
  if (dynamic_cast<const FnCall *>(&insn)) return "call";
  return "other";
}

std::string inspect(const Function &fn) {
  std::ostringstream out;
  out << "fn " << fn.getName() << " " << fn.getType().toString() << "\n";
  out << "mem" << fn.getFnAttrs().mem << "\n";
  for (auto &decl : fn.getFnDecls()) {
    out << "decl " << decl.name << " " << decl.output->toString() << " args " << decl.inputs.size();
    out << " mem" << decl.attrs.mem << " types=";
    for (auto &[type, attrs] : decl.inputs) out << attrs << type->toString() << ";";
    out << "\n";
  }
  for (auto &input : fn.getInputs())
    out << "in " << input.getName() << " " << input.getType().toString() << "\n";
  for (auto *bb : fn.getBBs()) {
    out << "bb " << bb->getName() << "\n";
    for (size_t i = 0; i < bb->size(); ++i) {
      auto &insn = bb->at(i);
      out << "  " << kind_of(insn) << " " << insn.getName() << " ty=" << insn.getType().toString() << " ops=";
      bool first = true;
      for (auto *operand : insn.operands()) {
        if (!first) out << ",";
        first = false;
        out << value_desc(*operand);
      }
      out << " targets=";
      if (auto *br = dynamic_cast<const Branch *>(&insn)) {
        out << br->getTrue().getName();
        if (br->getFalse())
          out << "," << br->getFalse()->getName();
      }
      out << " text=";
      insn.print(out);
      out << "\n";
    }
  }
  return out.str();
}

void configure_smoke(Function &fn) {
  num_ptrinputs = 0;
  for (auto &input : fn.getInputs()) num_ptrinputs += input.getType().isPtrType();
  num_locals_src = num_locals_tgt = num_globals_src = num_consts_src = 0;
  num_inaccessiblememonly_fns = 0;
  has_fncall = has_write_fncall = has_alloca = false;
  does_int_load = does_int_store = does_ptr_load = does_ptr_store = false;
  unsigned external = num_ptrinputs + 1;
  for (auto *global : fn.getGlobalVars()) {
    ++num_globals_src;
    num_consts_src += global->isConst();
    ++external;
  }
  for (auto &instruction : fn.instrs()) {
    if (dynamic_cast<const Alloc *>(&instruction)) { ++num_locals_src; has_alloca = true; }
    if (auto *call = dynamic_cast<const FnCall *>(&instruction)) {
      has_fncall = true;
      has_write_fncall |= call->getAttributes().mem.canWriteSomething();
      external += 2;
      ++num_inaccessiblememonly_fns;
    }
    if (auto *memory = dynamic_cast<const MemInstr *>(&instruction)) {
      auto info = memory->getByteAccessInfo();
      does_int_load |= info.doesIntLoad;
      does_int_store |= info.doesIntStore;
      does_ptr_load |= info.doesPtrLoad;
      does_ptr_store |= info.doesPtrStore;
      external += info.doesPtrLoad;
    }
  }
  num_nonlocals_src = num_nonlocals = external;
  bits_for_bid = 1 + std::bit_width(std::max(external, num_locals_src));
  bits_for_ptrattrs = 0;
  has_null_block = true;
  has_ptr_arg = num_ptrinputs != 0;
  has_int2ptr = has_nocapture = has_noread = has_nowrite = has_initializes_attr = false;
  has_globals_diff_align = has_indirect_fncalls = false;
}

std::string header() {
  return std::string(ALIVE_FILE) + "\n" + ALIVE2_PIN + "\n" + ROCQ_PIN + "\n";
}

void expect_has(const std::string &got, const std::string &needle) {
  if (got.find(needle) == std::string::npos)
    throw std::runtime_error("inspect missing `" + needle + "` in:\n" + got);
}

void expect_throw(const std::string &text, const std::string &needle) {
  try {
    Prog prog;
    load_text(prog, text);
  } catch (const std::exception &err) {
    if (std::string(err.what()).find(needle) == std::string::npos)
      throw std::runtime_error("expected `" + needle + "` but got " + err.what());
    return;
  }
  throw std::runtime_error("expected failure containing " + needle);
}

void self_test() {
  auto load = [](const std::string &body) {
    Prog prog;
    load_text(prog, header() + body);
    return inspect(*prog.fn);
  };
  expect_has(load("define i64 @arith(i64 %a) memory(none) {\nentry:\n  %s = add i64 %a, 1\n  ret i64 %s\n}\n"), "add %s ty=i64 ops=%a:i64,imm:i64:1");
  expect_has(load("define i64 @br(i1 %c, i64 %a) memory(none) {\nentry:\n  br i1 %c, label %yes, label %no\nyes:\n  ret i64 %a\nno:\n  ret i64 0\n}\n"), "br br ty=void ops=%c:i1 targets=%yes,%no");
  expect_has(load("define i64 @go(i64 %a) memory(none) {\nentry:\n  br label %next\nnext:\n  ret i64 %a\n}\n"), "targets=%next");
  expect_has(load("define i32 @phi(i1 %c, i32 %a) memory(none) {\nentry:\n  br i1 %c, label %left, label %right\nleft:\n  br label %join\nright:\n  br label %join\njoin:\n  %x = phi i32 [ 1, %left ], [ %a, %right ]\n  ret i32 %x\n}\n"), "phi %x ty=i32 ops=imm:i32:1,%a:i32");
  expect_has(load("define i8 @narrow(i1 %c) memory(none) {\nentry:\n  br i1 %c, label %left, label %right\nleft:\n  br label %join\nright:\n  br label %join\njoin:\n  %x = phi i8 [ 7, %left ], [ 8, %right ]\n  ret i8 %x\n}\n"), "imm:i8:7");
  expect_has(load("define i64 @div(i64 %a, i64 %b) memory(none) {\nentry:\n  %q = udiv i64 %a, %b\n  ret i64 %q\n}\n"), "udiv %q ty=i64");
  auto mem = load("declare ptr @bpf_map_lookup_elem(ptr, ptr) memory(argmem: read, inaccessiblemem: readwrite)\ndefine i64 @m(ptr %ctx, ptr %pkt) memory(argmem: readwrite, inaccessiblemem: readwrite) {\nentry:\n  ret i64 0\n}\n");
  expect_has(mem, "mem memory(argmem: readwrite, inaccessiblemem: readwrite)");
  expect_has(mem, "decl bpf_map_lookup_elem ptr args 2 mem memory(argmem: read, inaccessiblemem: readwrite)");
  expect_throw(std::string("; alive-file v2\n") + ALIVE2_PIN + "\n" + ROCQ_PIN + "\ndefine i64 @a() memory(none) {\nentry:\n  ret i64 0\n}\n", "unsupported alive-file");
  expect_throw(std::string(ALIVE_FILE) + "\n; alive2-pin 000\n" + ROCQ_PIN + "\ndefine i64 @a() memory(none) {\nentry:\n  ret i64 0\n}\n", "unsupported alive2 pin");
  expect_throw(header() + "define i64 @a() memory(argmem: execute) {\nentry:\n  ret i64 0\n}\n", "unknown memory");
  expect_throw("define i64 @a() memory(none) {\nentry:\n  ret i64 0\n}\n", "missing alive-file");

  expect_throw("define i64 @a() memory(none) {\nentry:\n  ret i64 0\n}\n" + header(), "header");
  expect_throw(header() + "define i64 @a() memory(none) {\nentry:\n  ret i64 0\n}\n" + header(), "header must precede");

  for (const auto &instruction : {"br i1 %c label %entry", "store i64 0 ptr %p align", "%x = gep ptr %p 1 x i64", "%x = zext i8 0 to", "%x = add i64 0", "%x = phi i64 [ 0 %entry"}) {
    expect_throw(header() + "define i64 @bad(i1 %c, ptr %p) memory(none) {\nentry:\n  " + instruction + "\n  ret i64 0\n}\n", "line ");
  }
  expect_throw(header() + "define i64 @bad(i32 %a) memory(none) {\nentry:\n  %x = add i64 %a, 1\n  ret i64 %x\n}\n", "type mismatch");
  expect_throw(header() + "define i64 @bad() memory(none) {\nentry:\n  ret i64 0\n  ret i64 1\n}\n", "after terminator");
  expect_throw(header() + "define i64 @bad() memory(none) {\nentry:\n  ret i64 0\nentry:\n  ret i64 1\n}\n", "duplicate block");
  expect_throw(header() + "define i64 @bad() memory(none) {\nentry:\n  br label %join\njoin:\n  %x = phi i64 [ 1, %missing ]\n  ret i64 %x\n}\n", "phi predecessors");
  expect_throw(header() + "define i64 @bad() memory(none) {\nentry:\n  ret i64 0\n", "closing brace");

  expect_throw(header() + "define i64 @bad(i1 %c) memory(none) {\nentry:\n  br i1 %c, label %left, label %right\nleft:\n  %x = add i64 1, 2\n  br label %right\nright:\n  ret i64 %x\n}\n", "does not dominate");
  expect_throw(header() + "declare ptr lookup(ptr) memory(argmem: read)\ndefine ptr @bad(ptr %p) memory(argmem: read) {\nentry:\n  %x = call ptr lookup(ptr %p) memory(none)\n  ret ptr %x\n}\n", "call memory attribute");
  auto called = load("declare ptr lookup(ptr) memory(argmem: read)\ndefine ptr @ok(ptr %p) memory(argmem: read) {\nentry:\n  %x = call ptr lookup(ptr %p)\n  ret ptr %x\n}\n");
  expect_has(called, "%x = call ptr lookup(ptr %p) memory(argmem: read)");

  Types types;
  Function built(types.i64, std::string("built"));
  built.getFnAttrs().mem.setCanAlsoAccess(MemoryAccess::Args);
  built.getFnAttrs().mem.setCanAlsoAccess(MemoryAccess::Inaccessible);
  auto input = std::make_unique<Input>(types.ptr, std::string("%ctx"));
  built.addInput(std::move(input));
  auto &block = built.getBB("%entry");
  auto constant = std::make_unique<IntConst>(types.i64, static_cast<int64_t>(0));
  Value &zero = *constant;
  built.addConstant(std::move(constant));
  block.addInstr(std::make_unique<Return>(types.i64, zero));
  std::ostringstream printed;
  built.print(printed);
  Prog reloaded;
  load_text(reloaded, header() + printed.str());
  auto left = inspect(built);
  auto right = inspect(*reloaded.fn);
  if (left != right)
    throw std::runtime_error("round trip mismatch\nbuilt:\n" + left + "loaded:\n" + right);
}

} // namespace


struct AliveModule::Impl { Prog program; };
AliveModule::~AliveModule() = default;
AliveModule::AliveModule(AliveModule &&) noexcept = default;
AliveModule &AliveModule::operator=(AliveModule &&) noexcept = default;
IR::Function &AliveModule::function() const { return *impl->program.fn; }
std::size_t AliveModule::blocks() const { return impl->program.blocks.size(); }
AliveModule load_alive_v1(const std::string &text) {
  AliveModule result;
  result.impl = std::make_unique<AliveModule::Impl>();
  load_text(result.impl->program, text);
  return result;
}
void configure_alive_execution(IR::Function &fn) { configure_smoke(fn); }
std::string inspect_alive_function(const IR::Function &fn) { return inspect(fn); }
std::string alive_file_header() { return header(); }
void alive_loader_self_test() { self_test(); }
