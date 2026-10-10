#!/usr/bin/env bash
# Nightly fmt + clippy for tooling/ workspace crates only.
# Does not install toolchains, run lake, or format path deps (e.g. ../xpost).
# Prereq: rustup nightly (+ rustfmt, clippy), lake build done, ../xpost present.
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
manifest="$root/tooling/Cargo.toml"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$root/tooling/target-nightly}"

if ! rustup run nightly rustc -vV >/dev/null 2>&1; then
  echo "error: nightly toolchain missing; run: rustup toolchain install nightly -c rustc -c cargo -c rustfmt -c clippy" >&2
  exit 1
fi

pkgs=(-p lean-binding -p server)

echo "==> fmt (nightly, workspace crates only)"
cargo +nightly fmt --manifest-path "$manifest" "${pkgs[@]}" -- --check

echo "==> clippy (nightly, target=$CARGO_TARGET_DIR)"
cargo +nightly clippy --manifest-path "$manifest" --workspace --all-targets -- \
  -D warnings \
  -D clippy::dbg_macro \
  -D clippy::todo \
  -D clippy::unimplemented

echo "==> ok"
