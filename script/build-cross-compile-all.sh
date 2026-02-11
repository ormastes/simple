#!/usr/bin/env bash
# Cross-compile seed + full Simple compiler for all 8 target platforms.
#
# Usage:
#   ./script/build-cross-compile-all.sh [--seed-only] [--targets=linux-arm64,windows-x86]
#
# Requirements:
#   - CMake toolchain files at seed/cmake/toolchains/*.cmake
#   - Cross-compilers: aarch64-linux-gnu-gcc, riscv64-linux-gnu-gcc,
#     x86_64-w64-mingw32-gcc, i686-w64-mingw32-gcc, clang
#   - Sysroots at /opt/sysroots/ (or /tmp/ paths for CI)
#   - Native bin/release/linux-x86_64/simple for full compiler builds

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
BUILD_DIR="$PROJECT_DIR/build"
TOOLCHAIN_DIR="$PROJECT_DIR/seed/cmake/toolchains"

ALL_TARGETS="linux-x86_64 linux-arm64 linux-riscv64 windows-x86_64 windows-x86 freebsd-x86_64 freebsd-x86 macos-arm64"
SEED_ONLY=false
TARGETS=""

# Parse arguments
for arg in "$@"; do
    case $arg in
        --seed-only)
            SEED_ONLY=true
            ;;
        --targets=*)
            TARGETS="${arg#*=}"
            ;;
    esac
done

if [ -z "$TARGETS" ]; then
    TARGETS="$ALL_TARGETS"
fi

# Convert comma-separated to space-separated
TARGETS="${TARGETS//,/ }"

echo "====================================="
echo "  Simple Cross-Compilation Builder"
echo "====================================="
echo "Targets: $TARGETS"
echo "Seed only: $SEED_ONLY"
echo ""

PASS=0
FAIL=0
SKIP=0

# ---- Phase 1: Build seed for each target ----
echo "--- Phase 1: Cross-compile seed ---"
for target in $TARGETS; do
    toolchain="$TOOLCHAIN_DIR/$target.cmake"
    if [ ! -f "$toolchain" ]; then
        echo "SKIP $target: no toolchain file at $toolchain"
        SKIP=$((SKIP + 1))
        continue
    fi

    echo -n "Building seed for $target... "
    target_build="$BUILD_DIR/$target"
    rm -rf "$target_build"

    if cmake -B "$target_build" "$PROJECT_DIR/seed" \
        -DCMAKE_TOOLCHAIN_FILE="$toolchain" \
        > "$target_build.cmake.log" 2>&1; then

        # Build just the core targets (skip test targets that may fail cross-compiling)
        if cmake --build "$target_build" --target seed --target seed_cpp --target spl_runtime \
            >> "$target_build.cmake.log" 2>&1; then
            echo "OK"
            PASS=$((PASS + 1))

            # Also try building the CRT (may not exist for all platforms)
            cmake --build "$target_build" --target all >> "$target_build.cmake.log" 2>&1 || true
        else
            echo "FAIL (build)"
            FAIL=$((FAIL + 1))
        fi
    else
        echo "FAIL (configure)"
        FAIL=$((FAIL + 1))
    fi
done

echo ""
echo "Seed results: $PASS pass, $FAIL fail, $SKIP skip"
echo ""

if [ "$SEED_ONLY" = true ]; then
    echo "Done (seed only)."
    exit $FAIL
fi

# ---- Phase 2: Cross-compile Simple programs via C codegen ----
echo "--- Phase 2: Cross-compile Simple programs via C codegen ---"

NATIVE_SIMPLE="$PROJECT_DIR/bin/release/linux-x86_64/simple"
if [ ! -x "$NATIVE_SIMPLE" ]; then
    NATIVE_SIMPLE="$PROJECT_DIR/bin/release/simple"
fi

if [ ! -x "$NATIVE_SIMPLE" ]; then
    echo "WARNING: No native Simple compiler found. Skipping C codegen phase."
    echo ""
    echo "====================================="
    echo "  Cross-Compilation Summary"
    echo "====================================="
    echo "Seed:     $PASS pass, $FAIL fail, $SKIP skip"
    echo "====================================="
    exit $FAIL
fi

echo "Using native compiler: $NATIVE_SIMPLE"

# The C code generator (gen_c_only.spl) handles a subset of Simple.
# It can cross-compile Simple programs but NOT the full compiler binary
# (which is a Rust-based interpreter/JIT — requires Rust cross-compilation).

SOURCE_FILE="${SOURCE_FILE:-}"
if [ -z "$SOURCE_FILE" ]; then
    echo "No SOURCE_FILE specified. Skipping C codegen cross-compilation."
    echo "Usage: SOURCE_FILE=myapp.spl ./script/build-cross-compile-all.sh"
    echo ""
    echo "====================================="
    echo "  Cross-Compilation Summary"
    echo "====================================="
    echo "Seed:     $PASS pass, $FAIL fail, $SKIP skip"
    echo "====================================="
    exit $FAIL
fi

# Generate C code once using native compiler
GEN_C="/tmp/simple_cross_generated.c"
echo -n "Generating C code from $SOURCE_FILE... "
if "$NATIVE_SIMPLE" "$PROJECT_DIR/src/app/compile/gen_c_only.spl" "$SOURCE_FILE" "$GEN_C" 2>/dev/null | grep -v DEBUG; then
    echo "OK ($(wc -c < "$GEN_C") bytes)"
else
    echo "FAIL"
    echo "C code generation failed. Source may use features not yet supported by c_codegen."
    exit 1
fi

OUTPUT_DIR="${OUTPUT_DIR:-$PROJECT_DIR/build/cross-output}"
FULL_PASS=0
FULL_FAIL=0
BASENAME=$(basename "$SOURCE_FILE" .spl)

for target in $TARGETS; do
    echo -n "Building $BASENAME for $target... "

    # Determine compiler and flags based on target
    COMMON_CFLAGS="-std=gnu11 -O2 -Wno-return-type"
    case $target in
        linux-x86_64)
            CC="clang"
            CFLAGS="$COMMON_CFLAGS"
            OUTPUT="$BASENAME"
            EXTRA="-lm"
            ;;
        linux-arm64)
            CC="aarch64-linux-gnu-gcc"
            CFLAGS="$COMMON_CFLAGS"
            OUTPUT="$BASENAME"
            EXTRA="-lm"
            ;;
        linux-riscv64)
            CC="riscv64-linux-gnu-gcc"
            CFLAGS="$COMMON_CFLAGS"
            OUTPUT="$BASENAME"
            EXTRA="-lm"
            ;;
        windows-x86_64)
            CC="x86_64-w64-mingw32-gcc"
            CFLAGS="$COMMON_CFLAGS"
            OUTPUT="$BASENAME.exe"
            EXTRA=""
            ;;
        windows-x86)
            CC="i686-w64-mingw32-gcc"
            CFLAGS="$COMMON_CFLAGS"
            OUTPUT="$BASENAME.exe"
            EXTRA=""
            ;;
        freebsd-x86_64)
            CC="clang"
            SYSROOT=""
            if [ -d /opt/sysroots/freebsd-x86_64/usr/include ]; then
                SYSROOT="/opt/sysroots/freebsd-x86_64"
            elif [ -d /tmp/freebsd-sysroot/usr/include ]; then
                SYSROOT="/tmp/freebsd-sysroot"
            fi
            CFLAGS="$COMMON_CFLAGS --target=x86_64-unknown-freebsd14 --sysroot=$SYSROOT -fuse-ld=lld"
            OUTPUT="$BASENAME"
            EXTRA="-lm"
            ;;
        freebsd-x86)
            CC="clang"
            SYSROOT=""
            if [ -d /opt/sysroots/freebsd-x86/usr/include ]; then
                SYSROOT="/opt/sysroots/freebsd-x86"
            elif [ -d /tmp/freebsd-i386-sysroot/usr/include ]; then
                SYSROOT="/tmp/freebsd-i386-sysroot"
            fi
            CFLAGS="$COMMON_CFLAGS --target=i686-unknown-freebsd13 --sysroot=$SYSROOT -fuse-ld=lld"
            OUTPUT="$BASENAME"
            EXTRA="-lm"
            ;;
        macos-arm64)
            CC="clang"
            SDK=""
            if [ -d /opt/sysroots/macos/MacOSX14.5.sdk/usr/include ]; then
                SDK="/opt/sysroots/macos/MacOSX14.5.sdk"
            elif [ -d /tmp/macos-sdk/MacOSX14.5.sdk/usr/include ]; then
                SDK="/tmp/macos-sdk/MacOSX14.5.sdk"
            fi
            CFLAGS="$COMMON_CFLAGS --target=aarch64-apple-darwin -isysroot $SDK -fuse-ld=lld"
            OUTPUT="$BASENAME"
            EXTRA=""
            ;;
        *)
            echo "SKIP (unknown target)"
            continue
            ;;
    esac

    TARGET_DIR="$OUTPUT_DIR/$target"
    mkdir -p "$TARGET_DIR"

    if $CC $CFLAGS -o "$TARGET_DIR/$OUTPUT" "$GEN_C" $EXTRA \
        2>"$TARGET_DIR/build.log"; then
        SIZE=$(wc -c < "$TARGET_DIR/$OUTPUT")
        echo "OK ($SIZE bytes)"
        FULL_PASS=$((FULL_PASS + 1))
    else
        echo "FAIL (see $TARGET_DIR/build.log)"
        FULL_FAIL=$((FULL_FAIL + 1))
    fi
done

echo ""
echo "Cross-compile results: $FULL_PASS pass, $FULL_FAIL fail"
echo ""

# ---- Summary ----
echo "====================================="
echo "  Cross-Compilation Summary"
echo "====================================="
echo "Seed:      $PASS pass, $FAIL fail, $SKIP skip"
echo "Programs:  $FULL_PASS pass, $FULL_FAIL fail"
echo "====================================="
echo ""
echo "Note: The full 'simple' compiler binary is a Rust-based interpreter/JIT."
echo "Cross-compiling it requires Rust cross-compilation (not yet automated)."
echo "The C codegen path works for Simple programs that use supported features."

TOTAL_FAIL=$((FAIL + FULL_FAIL))
exit $TOTAL_FAIL
