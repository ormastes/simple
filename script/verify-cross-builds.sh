#!/usr/bin/env bash
# Verify cross-compiled binaries for all target platforms.
#
# Usage:
#   ./script/verify-cross-builds.sh [--quick] [--targets=linux-arm64,windows-x86]
#
# Checks:
#   1. Binary exists and has correct file format (ELF/PE/Mach-O)
#   2. QEMU smoke test for Linux ARM64/RISC-V
#   3. Wine smoke test for Windows targets

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

ALL_TARGETS="linux-x86_64 linux-arm64 linux-riscv64 windows-x86_64 windows-x86 freebsd-x86_64 freebsd-x86 macos-arm64"
QUICK=false
TARGETS=""

for arg in "$@"; do
    case $arg in
        --quick) QUICK=true ;;
        --targets=*) TARGETS="${arg#*=}" ;;
    esac
done

if [ -z "$TARGETS" ]; then
    TARGETS="$ALL_TARGETS"
fi
TARGETS="${TARGETS//,/ }"

echo "====================================="
echo "  Cross-Build Verification"
echo "====================================="
echo ""

PASS=0
FAIL=0
SKIP=0

verify_target() {
    local target="$1"
    local build_dir="$PROJECT_DIR/build/$target"
    local release_dir="$PROJECT_DIR/bin/release/$target"

    echo "--- $target ---"

    # Determine expected format
    case $target in
        linux-x86_64)
            SEED_BIN="$build_dir/seed"
            FULL_BIN="$release_dir/simple"
            EXPECT_SEED="ELF 64-bit.*x86-64"
            EXPECT_FULL="ELF 64-bit.*x86-64"
            QEMU=""
            ;;
        linux-arm64)
            SEED_BIN="$build_dir/seed"
            FULL_BIN="$release_dir/simple"
            EXPECT_SEED="ELF 64-bit.*ARM aarch64"
            EXPECT_FULL="ELF 64-bit.*ARM aarch64"
            QEMU="qemu-aarch64 -L /usr/aarch64-linux-gnu"
            ;;
        linux-riscv64)
            SEED_BIN="$build_dir/seed"
            FULL_BIN="$release_dir/simple"
            EXPECT_SEED="ELF 64-bit.*RISC-V"
            EXPECT_FULL="ELF 64-bit.*RISC-V"
            QEMU="qemu-riscv64 -L /usr/riscv64-linux-gnu"
            ;;
        windows-x86_64)
            SEED_BIN="$build_dir/seed.exe"
            FULL_BIN="$release_dir/simple.exe"
            EXPECT_SEED="PE32\+.*x86-64"
            EXPECT_FULL="PE32\+.*x86-64"
            QEMU=""
            ;;
        windows-x86)
            SEED_BIN="$build_dir/seed.exe"
            FULL_BIN="$release_dir/simple.exe"
            EXPECT_SEED="PE32 .*Intel 80386"
            EXPECT_FULL="PE32 .*Intel 80386"
            QEMU=""
            ;;
        freebsd-x86_64)
            SEED_BIN="$build_dir/seed"
            FULL_BIN="$release_dir/simple"
            EXPECT_SEED="ELF 64-bit.*x86-64.*FreeBSD"
            EXPECT_FULL="ELF 64-bit.*x86-64.*FreeBSD"
            QEMU=""
            ;;
        freebsd-x86)
            SEED_BIN="$build_dir/seed"
            FULL_BIN="$release_dir/simple"
            EXPECT_SEED="ELF 32-bit.*Intel 80386.*FreeBSD"
            EXPECT_FULL="ELF 32-bit.*Intel 80386.*FreeBSD"
            QEMU=""
            ;;
        macos-arm64)
            SEED_BIN="$build_dir/seed"
            FULL_BIN="$release_dir/simple"
            EXPECT_SEED="Mach-O 64-bit.*arm64"
            EXPECT_FULL="Mach-O 64-bit.*arm64"
            QEMU=""
            ;;
    esac

    # Check seed binary
    if [ -f "$SEED_BIN" ]; then
        FILE_INFO=$(file "$SEED_BIN")
        if echo "$FILE_INFO" | grep -qP "$EXPECT_SEED"; then
            echo "  seed:    OK ($FILE_INFO)"
        else
            echo "  seed:    WRONG FORMAT ($FILE_INFO)"
            echo "           Expected: $EXPECT_SEED"
            return 1
        fi
    else
        echo "  seed:    MISSING ($SEED_BIN)"
    fi

    # Check full compiler binary
    if [ -f "$FULL_BIN" ]; then
        FILE_INFO=$(file "$FULL_BIN")
        if echo "$FILE_INFO" | grep -qP "$EXPECT_FULL"; then
            SIZE=$(wc -c < "$FULL_BIN")
            echo "  simple:  OK ($SIZE bytes)"
        else
            echo "  simple:  WRONG FORMAT ($FILE_INFO)"
            echo "           Expected: $EXPECT_FULL"
            return 1
        fi
    else
        echo "  simple:  NOT BUILT (run build-cross-compile-all.sh first)"
    fi

    # QEMU smoke test (only if not quick mode and QEMU available)
    if [ "$QUICK" = false ] && [ -n "$QEMU" ] && [ -f "$SEED_BIN" ]; then
        echo -n "  qemu:    "
        if command -v $(echo $QEMU | cut -d' ' -f1) &>/dev/null; then
            if timeout 10 $QEMU "$SEED_BIN" --help &>/dev/null; then
                echo "OK (seed runs under QEMU)"
            else
                echo "FAIL or no --help support"
            fi
        else
            echo "SKIP (QEMU not installed)"
        fi
    fi

    # Wine test for Windows
    if [ "$QUICK" = false ] && [[ "$target" == windows-* ]] && [ -f "$SEED_BIN" ]; then
        echo -n "  wine:    "
        if command -v wine &>/dev/null; then
            if timeout 10 wine "$SEED_BIN" --help &>/dev/null 2>&1; then
                echo "OK (seed runs under Wine)"
            else
                echo "FAIL or no --help support"
            fi
        else
            echo "SKIP (Wine not installed)"
        fi
    fi

    return 0
}

for target in $TARGETS; do
    if verify_target "$target"; then
        PASS=$((PASS + 1))
    else
        FAIL=$((FAIL + 1))
    fi
    echo ""
done

echo "====================================="
echo "  Verification: $PASS pass, $FAIL fail"
echo "====================================="

exit $FAIL
