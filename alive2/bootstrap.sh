#!/usr/bin/env bash
# Build the vendored Alive2 and the eBPF front end. Idempotent: rerunning it
# reconfigures nothing that is already built.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
upstream="$here/third_party/alive2"
build_type="${CMAKE_BUILD_TYPE:-Release}"
jobs="${JOBS:-$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 4)}"

for tool in cmake ninja clang++; do
  command -v "$tool" >/dev/null || { echo "missing $tool" >&2; exit 1; }
done

if [ ! -f "$upstream/CMakeLists.txt" ]; then
  echo "vendored Alive2 is missing at $upstream" >&2
  echo "see UPSTREAM.txt for the pinned commit" >&2
  exit 1
fi

if ! grep -q '#include <iterator>' "$upstream/ir/instr.cpp"; then
  echo "applying patches/clang-iterator.patch"
  patch -d "$upstream" -p1 --forward < "$here/patches/clang-iterator.patch"
fi

z3_prefix="${Z3_PREFIX:-}"
if [ -z "$z3_prefix" ]; then
  if pkg-config --exists z3 2>/dev/null; then
    z3_prefix="$(pkg-config --variable=prefix z3)"
  elif command -v brew >/dev/null && brew --prefix z3 >/dev/null 2>&1; then
    z3_prefix="$(brew --prefix z3)"
  else
    echo "cannot locate Z3; set Z3_PREFIX to its install prefix" >&2
    exit 1
  fi
fi
echo "Z3 prefix $z3_prefix"

cmake -S "$upstream" -B "$upstream/build" -G Ninja \
  -DCMAKE_BUILD_TYPE="$build_type" \
  -DBUILD_TV=OFF \
  -DZ3_INCLUDE_DIR="$z3_prefix/include"
cmake --build "$upstream/build" -j "$jobs"

cmake -S "$here" -B "$here/build" -G Ninja \
  -DCMAKE_BUILD_TYPE="$build_type" \
  -DALIVE2_BUILD="$upstream/build" \
  -DZ3_INCLUDE_DIR="$z3_prefix/include" \
  -DZ3_LIBRARY="$z3_prefix/lib/libz3${CMAKE_SHARED_LIB_SUFFIX:-.dylib}"
cmake --build "$here/build" -j "$jobs"

echo
echo "built $here/build/direct_ir, $here/build/ebpf_test, $here/build/ebpf_file"