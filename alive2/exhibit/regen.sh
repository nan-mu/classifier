#!/bin/sh
set -eu
root=$(CDPATH= cd -- "$(dirname "$0")/../.." && pwd)
cmake --build "$root/alive2/build" --target ebpf-concrete ebpf-exhibit
"$root/alive2/build/ebpf-concrete" --out "$root/alive2/build/exhibit-traces"
"$root/alive2/build/ebpf-exhibit" --traces "$root/alive2/build/exhibit-traces" \
  --json "$root/alive2/build/exhibit-symbolic.json" \
  --out "$root/alive2/exhibit/EXHIBIT.md"
