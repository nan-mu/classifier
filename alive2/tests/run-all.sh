#!/usr/bin/env bash
# The one command a reviewer reruns. Regenerates the committed logs, so a log
# diff is not the check: Alive2 orders SMT conjuncts by pointer hash, and that
# order varies between runs. The exit codes and PASS/FAIL counts are the check.
set -uo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/.." && pwd)"
cd "$root"

# Models are regenerated per run. Clearing them keeps the final count a statement
# about this run instead of an accumulation of earlier failures.
rm -f "$root"/counterexamples/*.smt2

status=0

run() {
  local name="$1" log="$2"
  shift 2
  if "$@" >"$log" 2>&1; then
    echo "PASS $name -> $log"
  else
    echo "FAIL $name -> $log (exit $?)"
    status=1
  fi
}

run direct_ir "$root/direct-ir.log" ./build/direct_ir
run ebpf_test "$root/ebpf-test.log" ./build/ebpf_test
run clang_e2e "$root/clang-e2e.log" bash "$here/run-clang-e2e.sh"

echo
printf '%-16s %s\n' direct-ir.log \
  "$(grep -c '^Solver check' "$root/direct-ir.log") solver checks, $(grep -c '^FAIL' "$root/direct-ir.log") failures"
for log in ebpf-test.log clang-e2e.log; do
  printf '%-16s PASS=%s FAIL=%s\n' "$log" \
    "$(grep -c '^PASS' "$root/$log")" "$(grep -c '^FAIL' "$root/$log")"
done

echo
echo "counterexamples written this run: $(ls counterexamples 2>/dev/null | wc -l | tr -d ' ')"
echo "expected: 8, one per intentional mutation"
exit "$status"