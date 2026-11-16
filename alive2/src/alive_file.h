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
