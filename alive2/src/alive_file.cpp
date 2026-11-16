#include "alive_file.h"
#include "ir/constant.h"
#include "ir/function.h"
#include "ir/instr.h"

#include <cctype>
#include <fstream>
#include <iostream>
#include <map>
#include <memory>
#include <sstream>
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
    int64_t n = std::stoll(text);
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
    if (std::isspace(static_cast<unsigned char>(c)) || c == ',' || c == '(' || c == ')') {
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

void parse_define(Prog &p, const std::vector<std::string> &tok) {
  if (tok.size() < 3 || tok[0] != "define" || tok[2].empty() || tok[2][0] != '@')
    throw std::runtime_error("malformed define");
  p.fn = std::make_unique<Function>(p.types.of(tok[1]), std::string(tok[2].substr(1)));
  for (size_t i = 3; i + 1 < tok.size(); ++i) {
    if (tok[i] == "memory" || tok[i].starts_with("memory"))
      break;
    if (tok[i] != "i64" && tok[i] != "ptr" && tok[i] != "i32" && tok[i] != "i8" && tok[i] != "i1" && tok[i] != "i16")
      continue;
    if (tok[i + 1].empty() || tok[i + 1][0] != '%')
      continue;
    auto in = std::make_unique<Input>(p.types.of(tok[i]), std::string(tok[i + 1]));
    p.def(tok[i + 1], *in);
    p.fn->addInput(std::move(in));
  }
}

void one_insn(Prog &p, int lineno, const std::vector<std::string> &t) {
  if (t.empty())
    return;
  auto need = [&](size_t n) {
    if (t.size() < n)
      bad(lineno, "truncated instruction");
  };
  if (t[0] == "br") {
    if (t.size() >= 3 && t[1].starts_with("i")) {
      need(6);
      auto &cond = p.use(t[1], t[2]);
      auto *yes = p.blocks.at(t[4]);
      auto *no = p.blocks.at(t[6]);
      p.cur->addInstr(std::make_unique<Branch>(cond, *yes, *no));
    } else {
      need(3);
      p.cur->addInstr(std::make_unique<Branch>(*p.blocks.at(t[2])));
    }
    return;
  }
  if (t[0] == "ret") {
    need(3);
    p.cur->addInstr(std::make_unique<Return>(p.types.of(t[1]), p.use(t[1], t[2])));
    return;
  }
  if (t[0] == "store") {
    need(6);
    auto &val = p.use(t[1], t[2]);
    auto &ptr = p.use(t[3], t[4]);
    uint64_t align = std::stoull(t[6]);
    p.cur->addInstr(std::make_unique<Store>(ptr, val, align));
    return;
  }
  need(3);
  if (t[1] != "=")
    bad(lineno, "expected assignment");
  const std::string &name = t[0];
  const std::string &op = t[2];
  if (op == "alloca") {
    need(5);
    auto &sz = p.use(t[3], t[4]);
    uint64_t align = std::stoull(t[6]);
    auto insn = std::make_unique<Alloc>(p.types.ptr, std::string(name), sz, nullptr, align);
    p.def(name, *insn);
    p.cur->addInstr(std::move(insn));
  } else if (op == "gep") {
    need(8);
    auto &base = p.use(t[3], t[4]);
    auto gep = std::make_unique<GEP>(p.types.ptr, std::string(name), base, false, false, false);
    size_t i = 5;
    while (i + 2 < t.size()) {
      uint64_t scale = std::stoull(t[i]);
      auto &idx = p.use(t[i + 2], t[i + 3]);
      gep->addIdx(scale, idx);
      i += 4;
    }
    p.def(name, *gep);
    p.cur->addInstr(std::move(gep));
  } else if (op == "load") {
    need(7);
    auto &ptr = p.use(t[4], t[5]);
    uint64_t align = std::stoull(t[7]);
    auto insn = std::make_unique<Load>(p.types.of(t[3]), std::string(name), ptr, align);
    p.def(name, *insn);
    p.cur->addInstr(std::move(insn));
  } else if (op == "zext" || op == "sext" || op == "trunc" || op == "ptrtoint" || op == "inttoptr") {
    need(6);
    auto kind = op == "zext" ? ConversionOp::ZExt : op == "sext" ? ConversionOp::SExt
               : op == "trunc" ? ConversionOp::Trunc : op == "ptrtoint" ? ConversionOp::Ptr2Int
               : ConversionOp::Int2Ptr;
    auto &src = p.use(t[3], t[4]);
    auto insn = std::make_unique<ConversionOp>(p.types.of(t[6]), std::string(name), src, kind);
    p.def(name, *insn);
    p.cur->addInstr(std::move(insn));
  } else if (op == "icmp") {
    need(6);
    auto &a = p.use(t[4], t[5]);
    auto &b = p.use(t[4], t[6]);
    auto insn = std::make_unique<ICmp>(p.types.i1, std::string(name), icmp(t[3]), a, b);
    p.def(name, *insn);
    p.cur->addInstr(std::move(insn));
  } else if (op == "phi") {
    auto phi = std::make_unique<Phi>(p.types.of(t[3]), std::string(name));
    Phi *raw = phi.get();
    p.def(name, *phi);
    p.cur->addInstr(std::move(phi));
    for (size_t i = 4; i + 3 < t.size(); i += 4) {
      if (t[i] != "[")
        bad(lineno, "malformed phi");
      p.phis.emplace_back(raw, t[i + 1], t[i + 2]);
    }
  } else if (op == "call") {
    need(5);
    std::string callee = t[4];
    if (!callee.empty() && callee[0] == '@')
      callee = callee.substr(1);
    auto call = std::make_unique<FnCall>(p.types.of(t[3]), std::string(name), std::move(callee));
    for (size_t i = 5; i + 1 < t.size(); i += 2)
      call->addArg(p.use(t[i], t[i + 1]), ParamAttrs());
    p.def(name, *call);
    p.cur->addInstr(std::move(call));
  } else {
    try {
      binop(op);
    } catch (const std::runtime_error &) {
      bad(lineno, "unknown opcode " + op);
    }
    need(5);
    auto &a = p.use(t[3], t[4]);
    auto &b = p.use(t[3], t[5]);
    auto insn = std::make_unique<BinOp>(p.types.of(t[3]), std::string(name), a, b, binop(op));
    p.def(name, *insn);
    p.cur->addInstr(std::move(insn));
  }
}

void load_text(Prog &p, const std::string &text) {
  std::stringstream in(text);
  std::string line;
  std::vector<std::pair<int, std::string>> body;
  int lineno = 0;
  bool saw = false;
  while (std::getline(in, line)) {
    ++lineno;
    auto cut = line.find(';');
    if (cut != std::string::npos) {
      auto comment = line.substr(cut);
      if (comment.find("alive-file v1") != std::string::npos)
        saw = true;
      line = line.substr(0, cut);
    }
    auto hash = line.find_first_not_of(" \t\r");
    if (hash == std::string::npos)
      continue;
    line = line.substr(hash);
    if (line == "}")
      continue;
    body.emplace_back(lineno, line);
  }
  if (!saw)
    throw std::runtime_error("missing alive-file v1 header");
  bool in_fn = false;
  for (auto &[no, line] : body) {
    auto t = tokens(line);
    if (t.empty())
      continue;
    if (t[0] == "declare")
      continue;
    if (t[0] == "define") {
      parse_define(p, t);
      in_fn = true;
      continue;
    }
    if (!in_fn)
      bad(no, "instruction before define");
    if (line.back() == ':') {
      auto label = "%" + line.substr(0, line.size() - 1);
      auto &bb = p.fn->getBB(label);
      p.blocks.emplace(label, &bb);
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
    } catch (const std::runtime_error &err) {
      if (std::string(err.what()).starts_with("line "))
        throw;
      bad(no, err.what());
    }
  }
  for (auto &[phi, val, bb] : p.phis) {
    auto it = p.vals.find(val);
    if (it == p.vals.end()) {
      Type *ty = &p.types.i64;
      if (!val.empty() && val[0] != '%')
        phi->addValue(p.imm(*ty, val), std::string(bb));
      else
        throw std::runtime_error("phi uses undefined value " + val);
    } else {
      phi->addValue(*it->second, std::string(bb));
    }
  }
}

} // namespace

struct AliveModule::Impl {
  Prog prog;
};

AliveModule::~AliveModule() = default;
AliveModule::AliveModule(AliveModule &&) noexcept = default;
AliveModule &AliveModule::operator=(AliveModule &&) noexcept = default;

IR::Function &AliveModule::function() const {
  return *impl->prog.fn;
}

std::size_t AliveModule::blocks() const {
  return impl->prog.blocks.size();
}

AliveModule load_alive_v1(const std::string &text) {
  AliveModule mod;
  mod.impl = std::make_unique<AliveModule::Impl>();
  load_text(mod.impl->prog, text);
  if (!mod.impl->prog.fn)
    throw std::runtime_error("alive file has no function");
  return mod;
}
