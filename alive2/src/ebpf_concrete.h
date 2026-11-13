#pragma once

#include <array>
#include <cstdint>
#include <filesystem>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <variant>
#include <vector>

struct Bv64 {
  uint64_t bits = 0;
};

enum class PtrRole { Code, Stack, Ctx, Other };

struct Ptr {
  PtrRole role = PtrRole::Other;
  uint64_t offset = 0;
};

using Obs = std::variant<Bv64, std::monostate, Ptr>;

struct RegFile {
  Obs r[10]{};
};

struct InsnPc {
  uint32_t index = 0;
};

struct ExitPc {};

using PcAfter = std::variant<InsnPc, ExitPc, std::monostate>;

enum class StepStatus { Next, Exit, Stuck, Ub, Incomplete, Unsupported };

struct Step {
  InsnPc pc;
  PcAfter pc_after;
  StepStatus status = StepStatus::Next;
  RegFile before;
  RegFile after;
  std::optional<Bv64> return_value;
  std::string source_hex;
};

enum class Exclusion { UndefEitherSide, NoR10, NoRax, MemoryEmptyOnly };
enum class MemorySummary { Empty, Changed };
enum class Producer { Ok, Failed };
enum class BugFlag { None, DivZeroAsUb };

struct Trace {
  std::string case_id;
  std::string bytes_hex;
  std::string bytes_sha256;
  std::vector<std::pair<uint8_t, Bv64>> inputs;
  BugFlag bug = BugFlag::None;
  std::array<Exclusion, 4> exclusions = {
      Exclusion::UndefEitherSide, Exclusion::NoR10, Exclusion::NoRax,
      Exclusion::MemoryEmptyOnly};
  MemorySummary memory = MemorySummary::Empty;
  Producer producer = Producer::Ok;
  std::vector<Step> steps;
};

enum class DivergenceKind {
  Header, Exclusion, Producer, StepCount, Pc, Source, Status,
  ReturnValue, PcAfter, Memory, Reg
};

struct Divergence {
  DivergenceKind kind = DivergenceKind::Header;
  int step = -1;
  std::optional<uint32_t> pc;
  std::string line;
};

struct Fixture {
  const char *id = "";
  const char *bytes_hex = "";
  std::vector<std::pair<uint8_t, uint64_t>> inputs;
  BugFlag bug = BugFlag::None;
  bool must_fail_div_zero = false;
  std::optional<uint64_t> sanity_r0;
};

const std::vector<Fixture> &kFixtures();

Trace stamp(const Fixture &fixture, Trace steps);
std::string word_at(std::string_view bytes_hex, InsnPc pc);

Trace alive2_trace(const std::vector<uint8_t> &code,
                   const std::vector<std::pair<uint8_t, Bv64>> &inputs,
                   BugFlag bug);

Trace parse_rocq_stream(std::string_view stdout_bytes);
std::optional<Divergence> first_divergence(const Trace &rocq, const Trace &alive);
bool negative_holds(const Divergence &found);

void write_trace(const std::filesystem::path &path, const Trace &trace);
Trace read_trace(const std::filesystem::path &path);
