#!/usr/bin/env bash
#
# Test Windows builds with both ClangCL and MinGW toolchains
#
# Usage:
#   ./test-windows-builds.sh [clangcl|mingw|all]
#
# Requirements:
#   - For ClangCL: Visual Studio Build Tools + LLVM
#   - For MinGW: LLVM-MinGW or MSYS2 with MinGW packages
#   - For cross-compile: x86_64-w64-mingw32-gcc on Linux

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# Color output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

log_info() {
    echo -e "${GREEN}[INFO]${NC} $*"
}

log_warn() {
    echo -e "${YELLOW}[WARN]${NC} $*"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $*"
}

# Detect platform
PLATFORM="$(uname -s)"
case "$PLATFORM" in
    Linux*)
        PLATFORM="Linux"
        ;;
    Darwin*)
        PLATFORM="macOS"
        ;;
    MINGW*|MSYS*|CYGWIN*)
        PLATFORM="Windows"
        ;;
    *)
        log_error "Unsupported platform: $PLATFORM"
        exit 1
        ;;
esac

log_info "Platform detected: $PLATFORM"

# Test ClangCL build (Windows only)
test_clangcl() {
    log_info "=== Testing ClangCL build (MSVC ABI) ==="

    if [[ "$PLATFORM" != "Windows" ]]; then
        log_warn "ClangCL build only supported on Windows, skipping"
        return 0
    fi

    # Check for clang-cl
    if ! command -v clang-cl &> /dev/null; then
        log_error "clang-cl not found. Install LLVM for Windows."
        return 1
    fi

    log_info "Found clang-cl: $(clang-cl --version | head -1)"

    # Clean previous build
    rm -rf build-clangcl
    mkdir -p build-clangcl
    cd build-clangcl

    # Configure
    log_info "Configuring with ClangCL toolchain..."
    cmake -G Ninja \
        -DCMAKE_TOOLCHAIN_FILE=../cmake/toolchains/windows-x86_64-clangcl.cmake \
        -DCMAKE_BUILD_TYPE=Release \
        .. || {
        log_error "CMake configuration failed"
        return 1
    }

    # Build
    log_info "Building with ClangCL..."
    ninja || {
        log_error "Build failed"
        return 1
    }

    # Test
    log_info "Running runtime tests..."
    if ./runtime_test.exe; then
        log_info "✅ ClangCL build: ALL TESTS PASSED"
    else
        log_error "❌ ClangCL build: TESTS FAILED"
        return 1
    fi

    cd ..
}

# Test MinGW build (Windows or Linux cross-compile)
test_mingw() {
    log_info "=== Testing MinGW Clang build (GCC ABI) ==="

    # Check for MinGW compiler
    if [[ "$PLATFORM" == "Linux" ]]; then
        # Cross-compilation
        if ! command -v x86_64-w64-mingw32-gcc &> /dev/null; then
            log_warn "MinGW cross-compiler not found. Install: sudo apt install mingw-w64"
            return 0
        fi
        log_info "Found MinGW cross-compiler: $(x86_64-w64-mingw32-gcc --version | head -1)"
    else
        # Native Windows with MinGW
        if ! command -v clang &> /dev/null; then
            log_error "clang not found. Install LLVM-MinGW or use MSYS2."
            return 1
        fi
        log_info "Found clang: $(clang --version | head -1)"
    fi

    # Clean previous build
    rm -rf build-mingw
    mkdir -p build-mingw
    cd build-mingw

    # Configure
    log_info "Configuring with MinGW toolchain..."
    cmake -G Ninja \
        -DCMAKE_TOOLCHAIN_FILE=../cmake/toolchains/windows-x86_64-mingw.cmake \
        -DCMAKE_BUILD_TYPE=Release \
        .. || {
        log_error "CMake configuration failed"
        return 1
    }

    # Build
    log_info "Building with MinGW..."
    ninja || {
        log_error "Build failed"
        return 1
    }

    # Test (skip on cross-compile unless Wine available)
    if [[ "$PLATFORM" == "Linux" ]]; then
        if command -v wine &> /dev/null; then
            log_info "Running runtime tests with Wine..."
            if wine ./runtime_test.exe; then
                log_info "✅ MinGW build: ALL TESTS PASSED"
            else
                log_error "❌ MinGW build: TESTS FAILED"
                return 1
            fi
        else
            log_warn "Wine not found, skipping runtime tests (build succeeded)"
            log_info "✅ MinGW cross-compile: BUILD SUCCEEDED (tests not run)"
        fi
    else
        log_info "Running runtime tests..."
        if ./runtime_test.exe; then
            log_info "✅ MinGW build: ALL TESTS PASSED"
        else
            log_error "❌ MinGW build: TESTS FAILED"
            return 1
        fi
    fi

    cd ..
}

# Main
MODE="${1:-all}"

case "$MODE" in
    clangcl)
        test_clangcl
        ;;
    mingw)
        test_mingw
        ;;
    all)
        FAILED=0
        test_clangcl || FAILED=1
        test_mingw || FAILED=1

        if [[ $FAILED -eq 0 ]]; then
            log_info "==================================="
            log_info "✅ ALL WINDOWS BUILDS SUCCEEDED"
            log_info "==================================="
        else
            log_error "==================================="
            log_error "❌ SOME WINDOWS BUILDS FAILED"
            log_error "==================================="
            exit 1
        fi
        ;;
    *)
        log_error "Unknown mode: $MODE"
        echo "Usage: $0 [clangcl|mingw|all]"
        exit 1
        ;;
esac

log_info "Done!"
