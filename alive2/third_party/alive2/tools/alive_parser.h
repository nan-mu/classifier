#pragma once

// Copyright (c) 2018-present The Alive2 Authors.
// Distributed under the MIT license that can be found in the LICENSE file.

#include "tools/transform.h"
#include "ir/function.h"
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace IR { class Type; }

namespace tools {

std::vector<Transform> parse(std::string_view buf);

// Rejects a transform. Does not wrap the function as f => f.
std::pair<std::string, IR::Function> parse_single(std::string_view buf);

struct parser_initializer {
  parser_initializer();
  ~parser_initializer();
};


struct ParseException {
  std::string str;
  unsigned lineno;

  ParseException(std::string &&str, unsigned lineno)
    : str(std::move(str)), lineno(lineno) {}
};

constexpr unsigned PARSER_READ_AHEAD = 20;

}
