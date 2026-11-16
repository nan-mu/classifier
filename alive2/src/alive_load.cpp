#include "alive_file.h"
#include "ir/function.h"

#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>

int main(int argc, char **argv) {
  if (argc != 2) {
    std::cerr << "usage: alive2-load <file.alive>\n";
    return 2;
  }
  std::ifstream in(argv[1]);
  if (!in) {
    std::cerr << "cannot read " << argv[1] << "\n";
    return 1;
  }
  std::stringstream buf;
  buf << in.rdbuf();
  try {
    AliveModule mod = load_alive_v1(buf.str());
    mod.function().print(std::cout);
    std::cout << "blocks " << mod.blocks() << "\n";
  } catch (const std::exception &err) {
    std::cerr << err.what() << "\n";
    return 1;
  }
  return 0;
}
