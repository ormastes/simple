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

# ---- Phase 2: Cross-compile full Simple compiler ----
echo "--- Phase 2: Cross-compile full compiler ---"

NATIVE_SIMPLE="$PROJECT_DIR/bin/release/linux-x86_64/simple"
if [ ! -x "$NATIVE_SIMPLE" ]; then
    NATIVE_SIMPLE="$PROJECT_DIR/bin/release/simple"
fi

if [ ! -x "$NATIVE_SIMPLE" ]; then
    echo "ERROR: No native Simple compiler found at bin/release/linux-x86_64/simple or bin/release/simple"
    echo "Cannot build full compiler without native bootstrap."
    exit 1
fi

echo "Using native compiler: $NATIVE_SIMPLE"

# Generate C code once using native compiler
GEN_C="/tmp/simple_generated.c"
echo -n "Generating C code from Simple source... "
if "$NATIVE_SIMPLE" compile src/app/cli/main.spl --backend=c --output="$GEN_C" 2>/dev/null; then
    echo "OK ($(wc -c < "$GEN_C") bytes)"
else
    echo "FAIL"
    echo "Cannot generate C code. Full compiler cross-compilation skipped."
    exit 1
fi

FULL_PASS=0
FULL_FAIL=0

for target in $TARGETS; do
    echo -n "Building full compiler for $target... "

    # Determine compiler and flags based on target
    case $target in
        linux-x86_64)
            CC="clang"
            CFLAGS="-O2"
            OUTPUT="simple"
            ;;
        linux-arm64)
            CC="aarch64-linux-gnu-gcc"
            CFLAGS="-O2"
            OUTPUT="simple"
            ;;
        linux-riscv64)
            CC="riscv64-linux-gnu-gcc"
            CFLAGS="-O2"
            OUTPUT="simple"
            ;;
        windows-x86_64)
            CC="x86_64-w64-mingw32-gcc"
            CFLAGS="-O2"
            OUTPUT="simple.exe"
            ;;
        windows-x86)
            CC="i686-w64-mingw32-gcc"
            CFLAGS="-O2"
            OUTPUT="simple.exe"
            ;;
        freebsd-x86_64)
            CC="clang"
            SYSROOT=""
            if [ -d /opt/sysroots/freebsd-x86_64/usr/include ]; then
                SYSROOT="/opt/sysroots/freebsd-x86_64"
            elif [ -d /tmp/freebsd-sysroot/usr/include ]; then
                SYSROOT="/tmp/freebsd-sysroot"
            fi
            CFLAGS="-O2 --target=x86_64-unknown-freebsd14 --sysroot=$SYSROOT -fuse-ld=lld"
            OUTPUT="simple"
            ;;
        freebsd-x86)
            CC="clang"
            SYSROOT=""
            if [ -d /opt/sysroots/freebsd-x86/usr/include ]; then
                SYSROOT="/opt/sysroots/freebsd-x86"
            elif [ -d /tmp/freebsd-i386-sysroot/usr/include ]; then
                SYSROOT="/tmp/freebsd-i386-sysroot"
            fi
            CFLAGS="-O2 --target=i686-unknown-freebsd13 --sysroot=$SYSROOT -fuse-ld=lld"
            OUTPUT="simple"
            ;;
        macos-arm64)
            CC="clang"
            SDK=""
            if [ -d /opt/sysroots/macos/MacOSX14.5.sdk/usr/include ]; then
                SDK="/opt/sysroots/macos/MacOSX14.5.sdk"
            elif [ -d /tmp/macos-sdk/MacOSX14.5.sdk/usr/include ]; then
                SDK="/tmp/macos-sdk/MacOSX14.5.sdk"
            fi
            CFLAGS="-O2 --target=aarch64-apple-darwin -isysroot $SDK -fuse-ld=lld"
            OUTPUT="simple"
            ;;
        *)
            echo "SKIP (unknown target)"
            continue
            ;;
    esac

    RELEASE_DIR="$PROJECT_DIR/bin/release/$target"
    mkdir -p "$RELEASE_DIR"

    if $CC $CFLAGS -o "$RELEASE_DIR/$OUTPUT" "$GEN_C" \
        "$PROJECT_DIR/seed/runtime.c" -I"$PROJECT_DIR/seed" \
        -lm 2>"$RELEASE_DIR/build.log"; then
        echo "OK ($(wc -c < "$RELEASE_DIR/$OUTPUT") bytes)"
        FULL_PASS=$((FULL_PASS + 1))
    else
        echo "FAIL (see $RELEASE_DIR/build.log)"
        FULL_FAIL=$((FULL_FAIL + 1))
    fi
done

echo ""
echo "Full compiler results: $FULL_PASS pass, $FULL_FAIL fail"
echo ""

# ---- Summary ----
echo "====================================="
echo "  Cross-Compilation Summary"
echo "====================================="
echo "Seed:     $PASS pass, $FAIL fail, $SKIP skip"
echo "Compiler: $FULL_PASS pass, $FULL_FAIL fail"
echo "====================================="

TOTAL_FAIL=$((FAIL + FULL_FAIL))
exit $TOTAL_FAIL
