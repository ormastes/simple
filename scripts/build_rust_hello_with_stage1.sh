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

# examples/simpleos_hello_rs/src/main.rs defines its own _start for the
# wave-4a path where crt0.o is not linked. The stage1 built-in target spec
# DOES pull in ${SDKROOT}/lib/crt0.o, which already provides _start — that
# would produce a duplicate-symbol link error. Stage a _start-less variant
# that still exercises libcore (PanicInfo) so the stage1 rlibs get linked.
SHIM_SRC_DIR="${SHIM_SRC_DIR:-/tmp/simpleos-stage1-src}"
mkdir -p "$SHIM_SRC_DIR"
cat >"$SHIM_SRC_DIR/hello_rs_stage1.rs" <<'RS'
// Stage1-sysroot smoke test: exercises libcore via PanicInfo & core::hint,
// links libsimpleos_c via the built-in target spec, lets crt0.o provide
// _start. Mirrors the shape of examples/simpleos_hello_rs/src/main.rs but
// without the duplicate _start.
#![no_std]
#![no_main]

use core::panic::PanicInfo;

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop { core::hint::spin_loop(); }
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    0
}
RS
STAGE1_SRC="$SHIM_SRC_DIR/hello_rs_stage1.rs"

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
echo "[stage1] shim:   $SHIM_DIR"
echo "[stage1] out:    $OUT"

# Bare triple — hits the compiled-in TargetOptions whose metadata hash
# matches the stage1 rlibs. cd into the shim so literal "${SDKROOT}/..."
# paths resolve through the symlink.
(
    cd "$SHIM_DIR"
    "$RUSTC" \
        --edition 2021 \
        --target "$TARGET_TRIPLE" \
        --sysroot "$SYSROOT" \
        -C opt-level=3 \
        -C panic=abort \
        -C link-arg=-L"$SYSROOT_LIB" \
        -o "$OUT" \
        "$STAGE1_SRC"
)

[ -f "$OUT" ] || { echo "error: artifact missing after rustc"; exit 6; }

echo ""
echo "==> OK no_std artifact: $OUT"
if [ -x "$LLVM_NM" ]; then
    "$LLVM_NM" "$OUT" | grep ' _start' || { echo "error: _start symbol missing"; exit 7; }
    # v0 mangling encodes crate name as `NtCs..._4core`/`_5alloc`/`_3std`.
    STD_SYMS="$("$LLVM_NM" "$OUT" | grep -cE '_(4core|5alloc|3std)' || true)"
    echo "[stage1] libcore/alloc/std symbol count (no_std build): $STD_SYMS"
fi
ls -la "$OUT"

# ---- Second smoke: libstd linkage ----
# The no_std build above only exercises libcore + libcompiler_builtins. To
# prove the stage1 libstd rlib is *usable* (not just present on disk), build
# a tiny program that allocates a String — which forces libstd, liballoc,
# libcompiler_builtins, panic_abort, and the global allocator to all link.
STD_SRC="$SHIM_SRC_DIR/std_smoke.rs"
OUT_STD="${OUT_STD:-/tmp/hello_std_stage1}"
cat >"$STD_SRC" <<'RS'
// Stage1 libstd linkage smoke. Uses -O1 + side-effect sink so the allocation
// is not dead-code-eliminated. crt0 provides _start; we define `main`.
#![no_main]
static mut SINK: usize = 0;
#[no_mangle]
pub extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    let s: std::string::String = std::string::String::from("hello simpleos");
    unsafe { SINK = s.len().wrapping_add(argc as usize); }
    core::mem::forget(s);
    0
}
RS
(
    cd "$SHIM_DIR"
    "$RUSTC" \
        --edition 2021 \
        --target "$TARGET_TRIPLE" \
        --sysroot "$SYSROOT" \
        -C opt-level=1 \
        -C panic=abort \
        -C link-arg=-L"$SYSROOT_LIB" \
        -o "$OUT_STD" \
        "$STD_SRC"
)
[ -f "$OUT_STD" ] || { echo "error: std artifact missing"; exit 8; }
echo ""
echo "==> OK std artifact:  $OUT_STD"
if [ -x "$LLVM_NM" ]; then
    STD_SYMS_STD="$("$LLVM_NM" "$OUT_STD" | grep -cE '_(4core|5alloc|3std)' || true)"
    echo "[stage1] libcore/alloc/std symbol count (libstd build): $STD_SYMS_STD"
    if [ "$STD_SYMS_STD" -lt 10 ]; then
        echo "error: libstd was not actually linked (<10 stdlib symbols)"
        exit 9
    fi
fi
ls -la "$OUT_STD"
