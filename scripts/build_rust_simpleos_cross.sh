#!/usr/bin/env bash
# build_rust_simpleos_cross.sh — Cross-compile Rust crate for SimpleOS target
# Sibling to scripts/build_llvm_simpleos_cross.sh (which must run first).
set -euo pipefail

# ---------------------------------------------------------------------------
# 1. Environment variables with defaults
# ---------------------------------------------------------------------------
RUST_SRC="${RUST_SRC:-$HOME/rust}"
TARGET="${TARGET:-x86_64-unknown-simpleos}"
SIMPLEOS_SYSROOT="${SIMPLEOS_SYSROOT:-$PWD/build/os/sysroot}"
LLVM_BUILD="${LLVM_BUILD:-$PWD/build/os/llvm/cross-x86_64}"
RUSTC_STAGE="${RUSTC_STAGE:-1}"

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TARGET_JSON="$REPO_ROOT/src/os/toolchain/rust/${TARGET}.json"
CRATE_DIR="$REPO_ROOT/src/compiler_rust"
ARTIFACT="$CRATE_DIR/target/${TARGET}/release/simple"

# ---------------------------------------------------------------------------
# 2. Preflight checks
# ---------------------------------------------------------------------------
echo "[preflight] checking prerequisites..."

# 2a. nightly toolchain — pinned to avoid rustc-literal-escaper vendoring mismatch
NIGHTLY_PIN="nightly-2024-09-01"
if ! rustup toolchain list 2>/dev/null | grep -q "${NIGHTLY_PIN}"; then
    echo "Installing pinned nightly toolchain ${NIGHTLY_PIN} ..."
    rustup toolchain install "${NIGHTLY_PIN}" --profile minimal --component rust-src
fi

# 2b. sysroot library
if [ ! -f "$SIMPLEOS_SYSROOT/lib/libsimpleos_c.a" ]; then
    echo "ERROR: sysroot library not found: $SIMPLEOS_SYSROOT/lib/libsimpleos_c.a"
    echo "  Fix: build the SimpleOS sysroot first (e.g. via the OS build system)"
    echo "       then re-export SIMPLEOS_SYSROOT to its installed location."
    exit 3
fi

# 2c. LLVM clang (linker)
if [ ! -f "$LLVM_BUILD/bin/clang" ]; then
    echo "ERROR: clang not found at $LLVM_BUILD/bin/clang"
    echo "  Fix: run scripts/build_llvm_simpleos_cross.sh first"
    exit 4
fi

# 2d. target JSON
if [ ! -f "$TARGET_JSON" ]; then
    echo "ERROR: target spec not found: $TARGET_JSON"
    echo "  Expected: src/os/toolchain/rust/${TARGET}.json"
    exit 5
fi

echo "[preflight] all checks passed."

# ---------------------------------------------------------------------------
# 3. Select build path
# ---------------------------------------------------------------------------
FORKED_RUSTC="$RUST_SRC/build/x86_64-unknown-linux-gnu/stage${RUSTC_STAGE}/bin/rustc"

if [ -f "$FORKED_RUSTC" ]; then
    echo "[path] Path B: using forked rustc at $FORKED_RUSTC"
    USE_FORKED=1
else
    echo "[path] Path A: using system nightly rustc (RUST_SRC not set or no built rustc found)"
    USE_FORKED=0
fi

# ---------------------------------------------------------------------------
# 4. Pre-link environment
# ---------------------------------------------------------------------------
export SDKROOT="$SIMPLEOS_SYSROOT"
export CC_x86_64_unknown_simpleos="$LLVM_BUILD/bin/clang"
export CARGO_TARGET_X86_64_UNKNOWN_SIMPLEOS_LINKER="$LLVM_BUILD/bin/clang"
export CARGO_TARGET_X86_64_UNKNOWN_SIMPLEOS_RUSTFLAGS="-C link-arg=--target=x86_64-simpleos -C link-arg=--sysroot=$SIMPLEOS_SYSROOT"

# ---------------------------------------------------------------------------
# 5. Compose cargo command
# ---------------------------------------------------------------------------
TARGET_JSON_REL="$TARGET_JSON"

if [ "$USE_FORKED" -eq 1 ]; then
    CARGO_CMD="RUSTC=$FORKED_RUSTC cargo build --release \
        --target $TARGET_JSON_REL"
else
    CARGO_CMD="cargo +nightly build --release \
        --target $TARGET_JSON_REL \
        -Z build-std=core,alloc,compiler_builtins \
        -Z build-std-features=compiler-builtins-mem"
fi

# ---------------------------------------------------------------------------
# 6. Dry-run gate
# ---------------------------------------------------------------------------
if [ "${RUST_BUILD_DRY_RUN:-0}" = "1" ]; then
    echo "[dry-run] would execute (in $CRATE_DIR):"
    echo "  $CARGO_CMD"
    exit 0
fi

# ---------------------------------------------------------------------------
# 7. Run the build
# ---------------------------------------------------------------------------
echo "[build] running cargo in $CRATE_DIR ..."
cd "$CRATE_DIR"

if [ "$USE_FORKED" -eq 1 ]; then
    RUSTC="$FORKED_RUSTC" cargo build --release \
        --target "$TARGET_JSON_REL"
else
    cargo +nightly build --release \
        --target "$TARGET_JSON_REL" \
        -Z build-std=core,alloc,compiler_builtins \
        -Z build-std-features=compiler-builtins-mem
fi

# ---------------------------------------------------------------------------
# 8. Report artifact
# ---------------------------------------------------------------------------
echo ""
echo "[done] artifact: $ARTIFACT"
ls -lh "$ARTIFACT"
