#include "ebpf_check.h"
#include "ebpf_ref.h"
#include "ebpf_run.h"
#include "smt/smt.h"

#include <fstream>
#include <iostream>
#include <string>
#include <vector>

namespace {

std::vector<uint8_t> read_bytes(const std::string &path) {
  std::ifstream in(path, std::ios::binary);
  if (!in)
    throw std::runtime_error("cannot open " + path);
  return std::vector<uint8_t>(std::istreambuf_iterator<char>(in),
                              std::istreambuf_iterator<char>());
}

void usage() {
  std::cerr << "usage: ebpf_file <bytecode> [--regs r1,r2] [--unroll N] "
               "[--no-check]\n";
}

} // namespace

int main(int argc, char **argv) {
  if (argc < 2) {
    usage();
    return 2;
  }
  std::string path = argv[1];
  std::vector<std::pair<uint8_t, std::string>> inputs = {{1, "r1"}};
  unsigned unroll = 0;
  bool run_checks = true;
  for (int i = 2; i < argc; ++i) {
    std::string arg = argv[i];
    if (arg == "--regs" && i + 1 < argc) {
      inputs.clear();
      std::string list = argv[++i];
      size_t start = 0;
      while (start <= list.size()) {
        size_t comma = list.find(',', start);
        std::string name = list.substr(start, comma == std::string::npos
                                                 ? std::string::npos
                                                 : comma - start);
        if (!name.empty()) {
          if (name.size() < 2 || name[0] != 'r')
            throw std::runtime_error("register name must look like r1: " + name);
          int reg = std::stoi(name.substr(1));
          if (reg < 0 || reg > 10)
            throw std::runtime_error("register out of range: " + name);
          inputs.emplace_back(static_cast<uint8_t>(reg), name);
        }
        if (comma == std::string::npos)
          break;
        start = comma + 1;
      }
    } else if (arg == "--unroll" && i + 1 < argc) {
      unroll = static_cast<unsigned>(std::stoul(argv[++i]));
    } else if (arg == "--no-check") {
      run_checks = false;
    } else {
      usage();
      return 2;
    }
  }

  smt::smt_initializer smt;
  try {
    auto e = execute_ebpf(read_bytes(path), inputs, unroll);
    print_sample(e);
    if (run_checks) {
      expect_equiv(e, path);
      expect_sweep(e, boundary_points(e), path);
    }
  } catch (const std::exception &err) {
    std::cerr << "ERROR " << err.what() << "\n";
    return 1;
  }
  if (g_failures) {
    std::cerr << g_failures << " checks failed\n";
    return 1;
  }
  std::cout << "\nall checks passed for " << path << "\n";
  return 0;
}