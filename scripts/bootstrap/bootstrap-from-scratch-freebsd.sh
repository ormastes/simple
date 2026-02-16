#!/bin/sh
# Bootstrap Simple Compiler From Scratch (FreeBSD)
#
# Builds the Simple compiler natively on FreeBSD with NO pre-existing Simple binary.
# Only requires: cmake, clang++ (or g++), and standard POSIX tools.
#
# Bootstrap chain:
#   1. cmake builds seed_cpp from seed/seed.cpp (C++ transpiler)
#   2. seed_cpp transpiles src/compiler_core/*.spl → C++
#   3. clang++ compiles C++ + runtime → Core1 (minimal native compiler)
#   4. Core1 compiles compiler_core → Core2 (self-hosting check)
#   5. Core2 compiles full compiler → Full1
#   6. Full1 recompiles itself → Full2 (reproducibility check)
#
# Usage:
#   ./scripts/bootstrap-from-scratch-freebsd.sh [options]
#
# Options:
#   --skip-verify     Skip reproducibility checks
#   --jobs=N          Parallel build jobs (default: auto-detect)
#   --cc=PATH         C++ compiler path (default: clang++)
#   --output=PATH     Final binary location (default: bin/simple)
#   --keep-artifacts  Keep build/bootstrap/ directory
#   --verbose         Show detailed command output
#   --help            Show this help

set -eu

# ============================================================================
# Configuration
# ============================================================================

SKIP_VERIFY=false
JOBS=""
CXX=""
OUTPUT="bin/simple"
KEEP_ARTIFACTS=false
VERBOSE=false
BUILD_DIR="build/bootstrap"
SEED_DIR="seed"
COMPILER_CORE_DIR="src/compiler_core"

# ============================================================================
# Argument parsing
# ============================================================================

for arg in "$@"; do
    case "$arg" in
        --skip-verify)    SKIP_VERIFY=true ;;
        --keep-artifacts) KEEP_ARTIFACTS=true ;;
        --verbose)        VERBOSE=true ;;
        --jobs=*)         JOBS="${arg#--jobs=}" ;;
        --cc=*)           CXX="${arg#--cc=}" ;;
        --output=*)       OUTPUT="${arg#--output=}" ;;
        --help)
            head -27 "$0" | tail -20
            exit 0
            ;;
        *)
            echo "Unknown option: $arg"
            echo "Run with --help for usage"
            exit 1
            ;;
    esac
done

# Auto-detect parallelism (FreeBSD uses sysctl)
if [ -z "$JOBS" ]; then
    if command -v sysctl >/dev/null 2>&1; then
        JOBS=$(sysctl -n hw.ncpu 2>/dev/null || echo 4)
    else
        JOBS=4
    fi
fi

# ============================================================================
# Helpers
# ============================================================================

log() { echo "[bootstrap] $*"; }
err() { echo "[bootstrap] ERROR: $*" >&2; }
run() {
    if [ "$VERBOSE" = true ]; then
        echo "+ $*" >&2
    fi
    "$@"
}

check_tool() {
    tool="$1"
    desc="$2"
    if ! command -v "$tool" >/dev/null 2>&1; then
        err "$tool not found. $desc"
        return 1
    fi
}

file_hash() {
    # FreeBSD uses sha256 command, not sha256sum
    if command -v sha256 >/dev/null 2>&1; then
        sha256 -q "$1" 2>/dev/null
    elif command -v sha256sum >/dev/null 2>&1; then
        sha256sum "$1" 2>/dev/null | cut -d' ' -f1
    else
        err "No SHA256 tool found. Install sha256 or coreutils."
        exit 1
    fi
}

# ============================================================================
# Platform detection
# ============================================================================

detect_platform() {
    os=$(uname -s | tr '[:upper:]' '[:lower:]')
    arch=$(uname -m)

    case "$os" in
        freebsd) OS_NAME="freebsd" ;;
        *)
            err "This script is for FreeBSD. Detected: $os"
            err "Use bootstrap-from-scratch.sh for Linux/macOS"
            err "Use bootstrap-from-scratch.bat for Windows"
            exit 1
            ;;
    esac

    case "$arch" in
        x86_64|amd64) ARCH_NAME="x86_64" ;;
        aarch64|arm64) ARCH_NAME="arm64" ;;
        riscv64)       ARCH_NAME="riscv64" ;;
        *)             ARCH_NAME="$arch" ;;
    esac

    PLATFORM="${OS_NAME}-${ARCH_NAME}"
}

# ============================================================================
# C++ compiler detection
# ============================================================================

find_cxx_compiler() {
    if [ -n "$CXX" ]; then
        if command -v "$CXX" >/dev/null 2>&1; then
            return 0
        fi
        err "Specified compiler not found: $CXX"
        return 1
    fi

    # FreeBSD default: clang++ (base system), then ports g++
    for candidate in clang++ g++ c++; do
        if command -v "$candidate" >/dev/null 2>&1; then
            CXX="$candidate"
            return 0
        fi
    done

    err "No C++ compiler found."
    err "FreeBSD base system should include clang++."
    err "If missing, install: pkg install llvm"
    return 1
}

# ============================================================================
# Step 0: Prerequisites
# ============================================================================

step0_prerequisites() {
    log "================================================================"
    log "Step 0: Checking prerequisites (FreeBSD)"
    log "================================================================"
    echo ""

    detect_platform
    log "Platform: $PLATFORM"

    find_cxx_compiler
    log "C++ compiler: $CXX ($($CXX --version 2>/dev/null | head -1))"

    check_tool cmake "Install cmake: pkg install cmake"
    log "cmake: $(cmake --version | head -1)"

    check_tool gmake "Install GNU make: pkg install gmake"
    log "gmake: $(gmake --version | head -1)"

    # Check seed source exists
    if [ ! -f "$SEED_DIR/seed.cpp" ]; then
        err "$SEED_DIR/seed.cpp not found. Are you in the project root?"
        exit 1
    fi
    log "Seed source: $SEED_DIR/seed.cpp"

    # Check compiler_core exists
    core_count=$(find "$COMPILER_CORE_DIR" -name '*.spl' 2>/dev/null | wc -l | tr -d ' ')
    if [ "$core_count" -eq 0 ]; then
        err "$COMPILER_CORE_DIR has no .spl files"
        exit 1
    fi
    log "Compiler core: $core_count .spl files in $COMPILER_CORE_DIR"

    echo ""
    log "All prerequisites OK"
    echo ""
}

# ============================================================================
# Step 1: Build seed compiler
# ============================================================================

step1_build_seed() {
    log "================================================================"
    log "Step 1: Building seed C++ transpiler"
    log "================================================================"
    echo ""

    mkdir -p "$BUILD_DIR/seed"
    cd "$BUILD_DIR/seed"

    log "Configuring cmake..."
    run cmake ../../"$SEED_DIR" \
        -DCMAKE_BUILD_TYPE=Release \
        -DCMAKE_CXX_COMPILER="$CXX" \
        -DCMAKE_VERBOSE_MAKEFILE="$VERBOSE"

    log "Building seed_cpp..."
    run gmake -j"$JOBS"

    cd ../..

    if [ ! -f "$BUILD_DIR/seed/seed_cpp" ]; then
        err "Seed compiler build failed: seed_cpp not found"
        exit 1
    fi

    log "Seed compiler ready: $BUILD_DIR/seed/seed_cpp"
    echo ""
}

# ============================================================================
# Step 2: Transpile compiler_core
# ============================================================================

step2_transpile_core() {
    log "================================================================"
    log "Step 2: Transpiling compiler_core to C++"
    log "================================================================"
    echo ""

    mkdir -p "$BUILD_DIR/core_cpp"

    log "Transpiling .spl → .cpp..."
    find "$COMPILER_CORE_DIR" -name '*.spl' -print0 | while IFS= read -r -d '' spl_file; do
        basename=$(basename "$spl_file" .spl)
        log "  $spl_file → $basename.cpp"
        run "$BUILD_DIR/seed/seed_cpp" "$spl_file" > "$BUILD_DIR/core_cpp/$basename.cpp"
    done

    cpp_count=$(find "$BUILD_DIR/core_cpp" -name '*.cpp' 2>/dev/null | wc -l | tr -d ' ')
    log "Generated $cpp_count C++ files"
    echo ""
}

# ============================================================================
# Step 3: Compile Core1 (minimal native compiler)
# ============================================================================

step3_compile_core1() {
    log "================================================================"
    log "Step 3: Compiling Core1 (minimal native compiler)"
    log "================================================================"
    echo ""

    mkdir -p "$BUILD_DIR/core1"

    log "Compiling C++ + runtime → Core1..."

    # Collect all generated C++ files
    cpp_files=$(find "$BUILD_DIR/core_cpp" -name '*.cpp')
    runtime_files="$SEED_DIR/runtime.c"

    # FreeBSD-specific: include platform header path
    platform_includes="-I$SEED_DIR/platform -DSPL_PLATFORM_FREEBSD"

    run "$CXX" -std=c++17 -O2 -o "$BUILD_DIR/core1/simple_core1" \
        $platform_includes \
        $cpp_files $runtime_files \
        -lpthread -lm

    if [ ! -f "$BUILD_DIR/core1/simple_core1" ]; then
        err "Core1 compilation failed"
        exit 1
    fi

    log "Core1 ready: $BUILD_DIR/core1/simple_core1"
    echo ""
}

# ============================================================================
# Step 4: Self-host Core2
# ============================================================================

step4_compile_core2() {
    log "================================================================"
    log "Step 4: Self-hosting Core2 (verify Core1 works)"
    log "================================================================"
    echo ""

    if [ "$SKIP_VERIFY" = true ]; then
        log "Skipping Core2 verification (--skip-verify)"
        echo ""
        return
    fi

    mkdir -p "$BUILD_DIR/core2"

    log "Core1 compiling compiler_core → Core2..."
    run "$BUILD_DIR/core1/simple_core1" \
        "$COMPILER_CORE_DIR" \
        -o "$BUILD_DIR/core2/simple_core2"

    if [ ! -f "$BUILD_DIR/core2/simple_core2" ]; then
        err "Core2 compilation failed"
        exit 1
    fi

    # Verify Core1 and Core2 are equivalent
    core1_hash=$(file_hash "$BUILD_DIR/core1/simple_core1")
    core2_hash=$(file_hash "$BUILD_DIR/core2/simple_core2")

    log "Core1 hash: $core1_hash"
    log "Core2 hash: $core2_hash"

    if [ "$core1_hash" = "$core2_hash" ]; then
        log "✓ Self-hosting verified (Core1 == Core2)"
    else
        log "⚠ Self-hosting hashes differ (expected for minimal core)"
    fi

    echo ""
}

# ============================================================================
# Step 5: Build Full1 (complete compiler)
# ============================================================================

step5_build_full1() {
    log "================================================================"
    log "Step 5: Building Full1 (complete compiler)"
    log "================================================================"
    echo ""

    mkdir -p "$BUILD_DIR/full1"

    # Use Core2 if verified, otherwise Core1
    if [ -f "$BUILD_DIR/core2/simple_core2" ] && [ "$SKIP_VERIFY" = false ]; then
        compiler="$BUILD_DIR/core2/simple_core2"
        log "Using Core2 to build Full1"
    else
        compiler="$BUILD_DIR/core1/simple_core1"
        log "Using Core1 to build Full1"
    fi

    log "Compiling full compiler source → Full1..."
    run "$compiler" src -o "$BUILD_DIR/full1/simple_full1"

    if [ ! -f "$BUILD_DIR/full1/simple_full1" ]; then
        err "Full1 compilation failed"
        exit 1
    fi

    log "Full1 ready: $BUILD_DIR/full1/simple_full1"
    echo ""
}

# ============================================================================
# Step 6: Reproducibility check
# ============================================================================

step6_verify_reproducible() {
    log "================================================================"
    log "Step 6: Reproducibility verification"
    log "================================================================"
    echo ""

    if [ "$SKIP_VERIFY" = true ]; then
        log "Skipping reproducibility verification (--skip-verify)"
        echo ""
        return
    fi

    mkdir -p "$BUILD_DIR/full2"

    log "Full1 recompiling itself → Full2..."
    run "$BUILD_DIR/full1/simple_full1" src -o "$BUILD_DIR/full2/simple_full2"

    if [ ! -f "$BUILD_DIR/full2/simple_full2" ]; then
        err "Full2 compilation failed"
        exit 1
    fi

    # Verify Full1 and Full2 are identical
    full1_hash=$(file_hash "$BUILD_DIR/full1/simple_full1")
    full2_hash=$(file_hash "$BUILD_DIR/full2/simple_full2")

    log "Full1 hash: $full1_hash"
    log "Full2 hash: $full2_hash"

    if [ "$full1_hash" = "$full2_hash" ]; then
        log "✓ Reproducibility verified (Full1 == Full2)"
    else
        err "✗ Reproducibility FAILED (Full1 != Full2)"
        err "The compiler produces different output when recompiling itself."
        exit 1
    fi

    echo ""
}

# ============================================================================
# Step 7: Install
# ============================================================================

step7_install() {
    log "================================================================"
    log "Step 7: Installing binary"
    log "================================================================"
    echo ""

    # Use verified Full2 if available, otherwise Full1
    if [ -f "$BUILD_DIR/full2/simple_full2" ] && [ "$SKIP_VERIFY" = false ]; then
        source_binary="$BUILD_DIR/full2/simple_full2"
        log "Using verified Full2 binary"
    else
        source_binary="$BUILD_DIR/full1/simple_full1"
        log "Using Full1 binary"
    fi

    # Create output directory
    output_dir=$(dirname "$OUTPUT")
    mkdir -p "$output_dir"

    # Copy binary
    run cp "$source_binary" "$OUTPUT"
    run chmod +x "$OUTPUT"

    log "Installed: $OUTPUT"

    # Verify
    if [ ! -f "$OUTPUT" ]; then
        err "Installation failed: $OUTPUT not found"
        exit 1
    fi

    # Test
    log "Testing installation..."
    version=$("$OUTPUT" --version 2>&1 | head -1 || echo "unknown")
    log "Version: $version"

    echo ""
}

# ============================================================================
# Step 8: Cleanup
# ============================================================================

step8_cleanup() {
    log "================================================================"
    log "Step 8: Cleanup"
    log "================================================================"
    echo ""

    if [ "$KEEP_ARTIFACTS" = true ]; then
        log "Keeping build artifacts (--keep-artifacts)"
        log "Location: $BUILD_DIR"
    else
        log "Removing build artifacts..."
        run rm -rf "$BUILD_DIR"
        log "Cleaned: $BUILD_DIR"
    fi

    echo ""
}

# ============================================================================
# Main
# ============================================================================

main() {
    log "========================================================"
    log "Simple Compiler Bootstrap (FreeBSD Native)"
    log "========================================================"
    echo ""

    step0_prerequisites
    step1_build_seed
    step2_transpile_core
    step3_compile_core1
    step4_compile_core2
    step5_build_full1
    step6_verify_reproducible
    step7_install
    step8_cleanup

    log "========================================================"
    log "Bootstrap Complete!"
    log "========================================================"
    echo ""
    log "Simple compiler installed: $OUTPUT"
    log "Platform: $PLATFORM"
    echo ""
    log "Next steps:"
    log "  1. Test: $OUTPUT --version"
    log "  2. Build: $OUTPUT build"
    log "  3. Test:  $OUTPUT test"
    echo ""
    log "Enjoy Simple on FreeBSD!"
}

main
