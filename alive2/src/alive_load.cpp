#include "alive_file.h"
#include "ir/function.h"
#include "ir/state.h"
#include "smt/smt.h"
#include "util/symexec.h"
#include <fstream>
#include <iostream>
#include <sstream>
#include <limits>
using namespace IR;

int main(int argc, char **argv) {
  if (argc == 2 && std::string(argv[1]) == "--self-test") {
    try {
      alive_loader_self_test();
    } catch (const std::exception &err) {
      std::cerr << err.what() << "\n";
      return 1;
    }
    std::cout << "alive2-load self-test ok\n";
    return 0;
  }
  bool dump = false;
  bool normalize = false;
  bool smoke = false;
  unsigned unroll = 0;
  const char *path = nullptr;
  if ((argc == 3 || argc == 5) && std::string(argv[1]) == "--smoke") {
    smoke = true;
    path = argv[2];
    if (argc == 5) {
      try {
        if (std::string(argv[3]) != "--unroll") throw std::runtime_error("expected --unroll");
        size_t used = 0;
        auto value = std::stoul(argv[4], &used);
        if (!value || used != std::string(argv[4]).size() || value > std::numeric_limits<unsigned>::max()) throw std::runtime_error("invalid unroll bound");
        unroll = value;
      } catch (const std::exception &err) {
        std::cerr << err.what() << "\n";
        return 2;
      }
    }
  } else if (argc == 3 && std::string(argv[1]) == "--normalize") {
    normalize = true;
    path = argv[2];
  } else if (argc == 3 && std::string(argv[1]) == "--inspect") {
    dump = true;
    path = argv[2];
  } else if (argc == 2) {
    path = argv[1];
  } else {
    std::cerr << "usage: alive2-load [--inspect | --normalize] <file.alive> | alive2-load --smoke <file.alive> [--unroll N] | alive2-load --self-test\n";
    return 2;
  }
  std::ifstream in(path);
  if (!in) {
    std::cerr << "cannot read " << path << "\n";
    return 1;
  }
  std::stringstream buf;
  buf << in.rdbuf();
  try {
    auto prog = load_alive_v1(buf.str());
    if (smoke) {
      LoopAnalysis loops(prog.function());
      if (!loops.getRoots().empty() && !unroll) throw std::runtime_error("loop smoke requires an explicit --unroll N bound");
      if (unroll) prog.function().unroll(unroll);
      prog.function().topSort();
      smt::smt_initializer smt;
      State::resetGlobals();
      configure_alive_execution(prog.function());
      State state(prog.function(), true);
      util::sym_exec(state);
      auto ret = state.returnVal();
      if (!ret.val.value.isValid() || !ret.return_domain.isValid() || !ret.domain().isValid())
        throw std::runtime_error("symbolic execution produced an invalid return state");
      std::cout << "smoke sym_exec completed; unroll " << unroll << "\n";
    } else if (normalize) {
      std::cout << alive_file_header();
      prog.function().print(std::cout);
    } else if (dump)
      std::cout << inspect_alive_function(prog.function());
    else {
      prog.function().print(std::cout);
      std::cout << "blocks " << prog.blocks() << "\n";
    }
  } catch (const std::exception &err) {
    std::cerr << err.what() << "\n";
    return 1;
  }
  return 0;
}
