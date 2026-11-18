#pragma once

#include <cstddef>
#include <memory>
#include <string>

namespace IR { class Function; }

struct AliveModule {
  struct Impl;
  std::unique_ptr<Impl> impl;

  AliveModule() = default;
  ~AliveModule();
  AliveModule(AliveModule &&) noexcept;
  AliveModule &operator=(AliveModule &&) noexcept;
  AliveModule(const AliveModule &) = delete;
  AliveModule &operator=(const AliveModule &) = delete;

  IR::Function &function() const;
  std::size_t blocks() const;
};

AliveModule load_alive_v1(const std::string &text);
void configure_alive_execution(IR::Function &fn);
std::string inspect_alive_function(const IR::Function &fn);
std::string alive_file_header();
void alive_loader_self_test();
