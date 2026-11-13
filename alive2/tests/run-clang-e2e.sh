#!/usr/bin/env bash
# Compile C to real eBPF machine code, then lift and symbolically execute it.
# The byte comparison against the independent ISA reference is the check; the
# compiler is only a source of realistic encodings.
set -uo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/.." && pwd)"
out="${E2E_OUT:-$root/build/e2e}"
mkdir -p "$out"

clang="${CLANG:-clang}"
objcopy="${OBJCOPY:-llvm-objcopy}"
cpu="${BPF_CPU:-v3}"
runner="$root/build/ebpf_file"

for tool in "$clang" "$objcopy"; do
  command -v "$tool" >/dev/null || { echo "missing $tool" >&2; exit 1; }
done
[ -x "$runner" ] || { echo "build ebpf_file first: $root/bootstrap.sh" >&2; exit 1; }

pass=0
fail=0
unsupported=0
for src in "$here"/bpf/*.c; do
  name="$(basename "$src" .c)"
  obj="$out/$name.o"
  bin="$out/$name.bin"
  log="$out/$name.log"
  if ! "$clang" -target bpf -mcpu="$cpu" -O2 -c "$src" -o "$obj" 2>"$out/$name.compile"; then
    echo "FAIL $name did not compile"
    cat "$out/$name.compile"
    fail=$((fail + 1))
    continue
  fi
  "$objcopy" -O binary --only-section=.text "$obj" "$bin" 2>/dev/null ||
    "$objcopy" -O binary --only-section=.text "$obj" "$bin"
  regs="r1"
  case "$name" in
    shift|udiv|arith) regs="r1,r2" ;;
  esac
  if "$runner" "$bin" --regs "$regs" >"$log" 2>&1; then
    echo "PASS $name ($(wc -c <"$bin" | tr -d ' ') bytes of .text)"
    pass=$((pass + 1))
  elif grep -q '^ERROR eBPF insn' "$log"; then
    echo "UNSUPPORTED $name: $(grep -m1 '^ERROR' "$log")"
    unsupported=$((unsupported + 1))
  else
    echo "FAIL $name, see $log"
    tail -5 "$log"
    fail=$((fail + 1))
  fi
done

echo
echo "clang e2e: $pass passed, $fail failed, $unsupported use opcodes outside this PoC"
[ "$fail" -eq 0 ]