#pragma once

#include "ir/constant.h"
#include "ir/function.h"
#include "ir/value.h"
#include <json-c/json.h>
#include <charconv>
#include <map>
#include <memory>
#include <set>
#include <stdexcept>
#include <string>

namespace explorer {
using Json = std::unique_ptr<json_object, decltype(&json_object_put)>;
inline Json parse_json(const std::string &text) {
  auto tok = std::unique_ptr<json_tokener, decltype(&json_tokener_free)>(json_tokener_new(), json_tokener_free);
  json_tokener_set_flags(tok.get(), JSON_TOKENER_STRICT);
  Json value(json_tokener_parse_ex(tok.get(), text.data(), static_cast<int>(text.size())), json_object_put);
  if (json_tokener_get_error(tok.get()) != json_tokener_success || !value)
    throw std::runtime_error("INITIAL_STATE_INVALID: invalid JSON");
  auto end = json_tokener_get_parse_end(tok.get());
  if (text.find_first_not_of(" \r\n\t", end) != std::string::npos)
    throw std::runtime_error("INITIAL_STATE_INVALID: trailing JSON content");
  return value;
}
inline json_object *field(json_object *object, const char *key) {
  json_object *value = nullptr;
  if (!json_object_is_type(object, json_type_object) || !json_object_object_get_ex(object, key, &value))
    throw std::runtime_error(std::string("INITIAL_STATE_INVALID: missing ") + key);
  return value;
}
inline std::string string_field(json_object *object, const char *key) {
  auto value = field(object, key);
  if (!json_object_is_type(value, json_type_string))
    throw std::runtime_error(std::string("INITIAL_STATE_INVALID: string required for ") + key);
  return std::string(json_object_get_string(value), json_object_get_string_len(value));
}
inline void keys(json_object *object, const std::set<std::string> &allowed) {
  if (!json_object_is_type(object, json_type_object)) throw std::runtime_error("INITIAL_STATE_INVALID: object required");
  json_object_object_foreach(object, key, value) {
    (void)value;
    if (!allowed.contains(key)) throw std::runtime_error(std::string("INITIAL_STATE_UNSUPPORTED: field ") + key);
  }
}
inline std::map<const IR::Value *, IR::Value *> initialize(IR::Function &fn, json_object *root) {
  keys(root, {"inputs"});
  auto inputs = field(root, "inputs");
  if (!json_object_is_type(inputs, json_type_array)) throw std::runtime_error("INITIAL_STATE_INVALID: inputs must be an array");
  std::map<std::string, json_object *> bindings;
  for (size_t i = 0; i < json_object_array_length(inputs); ++i) {
    auto row = json_object_array_get_idx(inputs, i);
    keys(row, {"name", "type", "kind", "value"});
    if (!bindings.emplace(string_field(row, "name"), row).second)
      throw std::runtime_error("INITIAL_STATE_INVALID: duplicate input");
  }
  std::map<const IR::Value *, IR::Value *> replacements;
  for (auto &input : fn.getInputs()) {
    auto found = bindings.find(input.getName());
    if (found == bindings.end()) throw std::runtime_error("INITIAL_STATE_INVALID: missing input " + input.getName());
    auto row = found->second;
    if (string_field(row, "type") != input.getType().toString()) throw std::runtime_error("INITIAL_STATE_INVALID: input type mismatch " + input.getName());
    auto kind = string_field(row, "kind");
    std::unique_ptr<IR::Value> value;
    if (kind == "concrete") {
      if (!input.getType().isIntType()) throw std::runtime_error("INITIAL_STATE_UNSUPPORTED: concrete pointer/object binding");
      if (input.getType().bits() > 64) throw std::runtime_error("INITIAL_STATE_UNSUPPORTED: concrete integers wider than 64 bits");
      auto digits = string_field(row, "value");
      if (digits.empty()) throw std::runtime_error("INITIAL_STATE_INVALID: empty integer");
      bool negative = digits[0] == '-';
      if (digits.size() == (negative ? 1u : 0u) || digits.find_first_not_of("0123456789", negative ? 1 : 0) != std::string::npos)
        throw std::runtime_error("INITIAL_STATE_INVALID: decimal integer required");
      uint64_t number = 0;
      if (negative) {
        int64_t signed_number = 0;
        auto result = std::from_chars(digits.data(), digits.data() + digits.size(), signed_number);
        if (result.ec != std::errc()) throw std::runtime_error("INITIAL_STATE_INVALID: integer outside input width");
        number = static_cast<uint64_t>(signed_number);
      } else {
        auto result = std::from_chars(digits.data(), digits.data() + digits.size(), number);
        if (result.ec != std::errc()) throw std::runtime_error("INITIAL_STATE_INVALID: integer outside input width");
      }
      auto width = input.getType().bits();
      if (width < 64 && (negative ? static_cast<int64_t>(number) < -(int64_t(1) << (width - 1)) : number >= (uint64_t(1) << width)))
        throw std::runtime_error("INITIAL_STATE_INVALID: integer outside input width");
      value = std::make_unique<IR::IntConst>(input.getType(), static_cast<int64_t>(number));
    } else if (kind == "undefined") {
      value = std::make_unique<IR::UndefValue>(input.getType());
    } else if (kind == "poison") {
      value = std::make_unique<IR::PoisonValue>(input.getType());
    } else if (kind != "symbolic") {
      throw std::runtime_error("INITIAL_STATE_UNSUPPORTED: input kind " + kind);
    }
    json_object *unused;
    if (kind != "concrete" && json_object_object_get_ex(row, "value", &unused))
      throw std::runtime_error("INITIAL_STATE_INVALID: value only allowed for concrete inputs");
    if (value) {
      fn.rauw(input, *value);
      replacements.emplace(&input, value.get());
      fn.addConstant(std::move(value));
    }
    bindings.erase(found);
  }
  if (!bindings.empty()) throw std::runtime_error("INITIAL_STATE_INVALID: unknown input " + bindings.begin()->first);
  return replacements;
}
} // namespace explorer
