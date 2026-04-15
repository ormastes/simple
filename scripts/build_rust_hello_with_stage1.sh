#!/usr/bin/env bash
# Phase-3 step-5 proof via the Rust fork's stage1 sysroot.
#
# Cross-compiles examples/simpleos_hello_rs/src/main.rs using rustc from
# `./x.py build library --target x86_64-unknown-simpleos --stage 1` directly,
# i.e. linking against the pre-built stage1 rlibs (libstd, libcore, liballoc,
# libcompiler_builtins) instead of rebuilding core+compiler_builtins from
# crates.io via `-Z build-std`.
#
# Companion to scripts/build_rust_hello_simpleos.sh (the wave-4a cargo +
# build-std recipe). This script validates that the stage1 sysroot itself
# is directly usable by rustc.
#
# IMPORTANT: the fork compiles x86_64-unknown-simpleos in as a BUILT-IN
# target spec (see /home/ormastes/rust/compiler/rustc_target/src/spec/targets/
# x86_64_unknown_simpleos.rs). Passing --target as a plain triple hits the
# built-in spec whose hash matches the rlib metadata. Passing a JSON file
# instead — even a byte-identical one — re-hashes the spec and mismatches.
# So this script uses the triple, NOT the JSON.
#
# NOTE: examples/simpleos_hello_rs/src/main.rs is `#![no_std] #![no_main]`,
# so only libcore + libcompiler_builtins are actually linked. libstd rlib
# existence is verified on disk but not pulled into the final binary.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RUST_ROOT="${RUST_ROOT:-$HOME/rust}"
STAGE1_HOST="${STAGE1_HOST:-x86_64-unknown-linux-gnu}"
STAGE1_DIR="$RUST_ROOT/build/$STAGE1_HOST/stage1"
RUSTC="$STAGE1_DIR/bin/rustc"
SYSROOT="$STAGE1_DIR"
TARGET_TRIPLE="${TARGET_TRIPLE:-x86_64-unknown-simpleos}"
SIMPLEOS_SYSROOT="${SIMPLEOS_SYSROOT:-$REPO_ROOT/build/os/sysroot}"
SYSROOT_LIB="$SIMPLEOS_SYSROOT/lib"
SRC="$REPO_ROOT/examples/simpleos_hello_rs/src/main.rs"
OUT="${OUT:-/tmp/hello_rs_stage1}"
LLVM_NM="$REPO_ROOT/build/os/llvm/cross-x86_64/bin/llvm-nm"

[ -x "$RUSTC" ] || { echo "error: stage1 rustc missing at $RUSTC"; exit 2; }

STAGE1_RLIBS="$SYSROOT/lib/rustlib/$TARGET_TRIPLE/lib"
if ! ls "$STAGE1_RLIBS"/libstd-*.rlib >/dev/null 2>&1; then
    echo "error: stage1 libstd rlib missing in $STAGE1_RLIBS"
    echo "  rerun in $RUST_ROOT: ./x.py build library --target $TARGET_TRIPLE --stage 1"
    exit 3
fi

[ -f "$SYSROOT_LIB/libsimpleos_c.a" ] || {
    echo "error: sysroot libc missing at $SYSROOT_LIB/libsimpleos_c.a"
    exit 4
}
[ -f "$SRC" ] || { echo "error: hello_rs source missing at $SRC"; exit 5; }

# The built-in target spec's pre-link-args hard-code the LITERAL string
# "${SDKROOT}/share/simpleos/simpleos.ld" and "${SDKROOT}/lib/crt0.o"
# (rust-lld does NOT env-expand those paths). Work around this by building
# a shim directory whose literal child name is "${SDKROOT}" and symlinks to
# the real sysroot, then invoking rustc from that cwd so relative paths
# resolve correctly.
SHIM_DIR="${SHIM_DIR:-/tmp/simpleos-stage1-shim}"
rm -rf "$SHIM_DIR"
mkdir -p "$SHIM_DIR"
ln -sf "$SIMPLEOS_SYSROOT" "$SHIM_DIR/\${SDKROOT}"

mkdir -p "$(dirname "$OUT")"

echo "[stage1] rustc: $RUSTC"
echo "[stage1] sysroot: $SYSROOT"
echo "[stage1] target: $TARGET_TRIPLE (built-in)"
echo "[stage1] SDKROOT: $SDKROOT"
echo "[stage1] out: $OUT"

# Bare triple — hits the compiled-in TargetOptions whose metadata hash matches
# the stage1 rlibs. Extra -L passes libsimpleos_c's directory without editing
# any spec file.
"$RUSTC" \
    --edition 2021 \
    --target "$TARGET_TRIPLE" \
    --sysroot "$SYSROOT" \
    -C opt-level=3 \
    -C panic=abort \
    -C link-arg=-L"$SYSROOT_LIB" \
    -o "$OUT" \
    "$SRC"

[ -f "$OUT" ] || { echo "error: artifact missing after rustc"; exit 6; }

echo ""
echo "==> OK: $OUT"
if [ -x "$LLVM_NM" ]; then
    "$LLVM_NM" "$OUT" | grep ' _start' || { echo "error: _start symbol missing"; exit 7; }
    STD_SYMS="$("$LLVM_NM" "$OUT" | grep -cE '(core|alloc|std)::' || true)"
    echo "[stage1] stdlib-symbol count (core/alloc/std::): $STD_SYMS"
else
    echo "warn: $LLVM_NM not found, skipping symbol check"
fi
ls -la "$OUT"
