#!/bin/bash
# Bootstrap Simple Compiler From Scratch
#
# Builds the Simple compiler on a machine with NO pre-existing Simple binary.
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
#   ./script/bootstrap-from-scratch.sh [options]
#
# Options:
#   --skip-verify     Skip reproducibility checks
#   --jobs=N          Parallel build jobs (default: auto-detect)
#   --cc=PATH         C++ compiler path (default: clang++)
#   --output=PATH     Final binary location (default: bin/simple)
#   --keep-artifacts  Keep build/bootstrap/ directory
#   --verbose         Show detailed command output
#   --help            Show this help

set -euo pipefail

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

# Auto-detect parallelism
if [ -z "$JOBS" ]; then
    if command -v nproc >/dev/null 2>&1; then
        JOBS=$(nproc)
    elif command -v sysctl >/dev/null 2>&1; then
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
    local tool="$1"
    local desc="$2"
    if ! command -v "$tool" >/dev/null 2>&1; then
        err "$tool not found. $desc"
        return 1
    fi
}

file_hash() {
    sha256sum "$1" 2>/dev/null | cut -d' ' -f1 || shasum -a 256 "$1" 2>/dev/null | cut -d' ' -f1
}

# ============================================================================
# Platform detection
# ============================================================================

detect_platform() {
    local os arch
    os=$(uname -s | tr '[:upper:]' '[:lower:]')
    arch=$(uname -m)

    case "$os" in
        linux)   OS_NAME="linux" ;;
        darwin)  OS_NAME="macos" ;;
        freebsd) OS_NAME="freebsd" ;;
        mingw*|msys*|cygwin*) OS_NAME="windows" ;;
        *)       OS_NAME="$os" ;;
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

    for candidate in clang++ g++ c++; do
        if command -v "$candidate" >/dev/null 2>&1; then
            CXX="$candidate"
            return 0
        fi
    done

    err "No C++ compiler found. Install clang++ or g++."
    return 1
}

# ============================================================================
# Step 0: Prerequisites
# ============================================================================

step0_prerequisites() {
    log "================================================================"
    log "Step 0: Checking prerequisites"
    log "================================================================"
    echo ""

    detect_platform
    log "Platform: $PLATFORM"

    find_cxx_compiler
    log "C++ compiler: $CXX ($($CXX --version 2>/dev/null | head -1))"

    check_tool cmake "Install cmake (https://cmake.org)"
    log "cmake: $(cmake --version | head -1)"

    check_tool make "Install make (build-essential on Debian/Ubuntu)"

    # Check seed source exists
    if [ ! -f "$SEED_DIR/seed.cpp" ]; then
        err "$SEED_DIR/seed.cpp not found. Are you in the project root?"
        exit 1
    fi
    log "Seed source: $SEED_DIR/seed.cpp"

    # Check compiler_core exists
    local core_count
    core_count=$(find "$COMPILER_CORE_DIR" -name '*.spl' 2>/dev/null | wc -l)
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
    log "Step 1: Building seed compiler (cmake + $CXX)"
    log "================================================================"
    echo ""

    mkdir -p "$SEED_DIR/build"

    # Configure with cmake
    log "Configuring with cmake..."
    run cmake -S "$SEED_DIR" -B "$SEED_DIR/build" \
        -DCMAKE_CXX_COMPILER="$CXX" \
        -DCMAKE_C_COMPILER="$(echo "$CXX" | sed 's/++$//' | sed 's/clang$/clang/' | sed 's/g$/gcc/')" \
        ${VERBOSE:+-DCMAKE_VERBOSE_MAKEFILE=ON} \
        >/dev/null 2>&1 || run cmake -S "$SEED_DIR" -B "$SEED_DIR/build"

    # Build
    log "Building seed_cpp + runtime (${JOBS} jobs)..."
    run cmake --build "$SEED_DIR/build" --parallel "$JOBS"

    # Verify artifacts
    if [ ! -f "$SEED_DIR/build/seed_cpp" ]; then
        err "seed_cpp binary not built"
        exit 1
    fi
    log "seed_cpp: $(wc -c < "$SEED_DIR/build/seed_cpp") bytes"

    if [ ! -f "$SEED_DIR/build/libspl_runtime.a" ]; then
        err "libspl_runtime.a not built"
        exit 1
    fi
    log "libspl_runtime.a: $(wc -c < "$SEED_DIR/build/libspl_runtime.a") bytes"

    # Check for startup CRT (platform-specific)
    local crt_path="$SEED_DIR/build/startup/libspl_crt_${OS_NAME}_${ARCH_NAME}.a"
    if [ -f "$crt_path" ]; then
        log "CRT: $crt_path ($(wc -c < "$crt_path") bytes)"
    else
        log "CRT: not found at $crt_path (using standard C++ startup)"
    fi

    echo ""
    log "Seed compiler built successfully"
    echo ""
}

# ============================================================================
# Step 2: Core1 — seed_cpp transpiles compiler_core to native
# ============================================================================

step2_core1() {
    log "================================================================"
    log "Step 2: Core1 (seed_cpp -> C++ -> $CXX -> native)"
    log "================================================================"
    echo ""

    mkdir -p "$BUILD_DIR"

    # Discover and order .spl files: __init__.spl first, main.spl last, rest sorted
    local init_file="" main_file=""
    local -a other_files=()

    while IFS= read -r f; do
        case "$f" in
            */__init__.spl) init_file="$f" ;;
            */main.spl)     main_file="$f" ;;
            *)              other_files+=("$f") ;;
        esac
    done < <(find "$COMPILER_CORE_DIR" -name '*.spl' | sort)

    local -a ordered=()
    [ -n "$init_file" ] && ordered+=("$init_file")
    ordered+=("${other_files[@]}")
    [ -n "$main_file" ] && ordered+=("$main_file")

    log "Found ${#ordered[@]} .spl files"

    # Transpile to C++
    log "Transpiling with seed_cpp..."
    run "$SEED_DIR/build/seed_cpp" "${ordered[@]}" > "$BUILD_DIR/core1.cpp"

    local cpp_size
    cpp_size=$(wc -c < "$BUILD_DIR/core1.cpp")
    log "Generated C++: $cpp_size bytes"

    if [ "$cpp_size" -lt 1000 ]; then
        err "C++ output too small ($cpp_size bytes) — seed_cpp likely failed"
        exit 1
    fi

    # Compile C++ to native
    log "Compiling with $CXX..."
    local compile_flags="-std=c++20 -O2"
    local link_flags="-I$SEED_DIR -L$SEED_DIR/build -lspl_runtime -lm -lpthread"

    if [ "$OS_NAME" = "linux" ]; then
        link_flags="$link_flags -ldl"
    fi

    run $CXX $compile_flags -o "$BUILD_DIR/core1" "$BUILD_DIR/core1.cpp" $link_flags

    if [ ! -f "$BUILD_DIR/core1" ]; then
        err "Core1 binary not created"
        exit 1
    fi

    chmod +x "$BUILD_DIR/core1"

    local bin_size
    bin_size=$(wc -c < "$BUILD_DIR/core1")
    log "Core1 binary: $bin_size bytes"

    # Smoke test
    if run "$BUILD_DIR/core1" --version >/dev/null 2>&1; then
        log "Smoke test: $("$BUILD_DIR/core1" --version 2>/dev/null | head -1)"
    else
        log "Smoke test: --version not supported (may be OK for minimal compiler)"
    fi

    echo ""
    log "Core1 built successfully"
    echo ""
}

# ============================================================================
# Step 3: Core2 — Core1 recompiles compiler_core
# ============================================================================

step3_core2() {
    log "================================================================"
    log "Step 3: Core2 (Core1 recompiles compiler_core)"
    log "================================================================"
    echo ""

    run "$BUILD_DIR/core1" compile "$COMPILER_CORE_DIR/main.spl" -o "$BUILD_DIR/core2"

    if [ ! -f "$BUILD_DIR/core2" ]; then
        err "Core2 binary not created"
        exit 1
    fi

    chmod +x "$BUILD_DIR/core2"

    local bin_size
    bin_size=$(wc -c < "$BUILD_DIR/core2")
    log "Core2 binary: $bin_size bytes"

    if [ "$SKIP_VERIFY" = false ]; then
        local hash1 hash2
        hash1=$(file_hash "$BUILD_DIR/core1")
        hash2=$(file_hash "$BUILD_DIR/core2")
        if [ "$hash1" = "$hash2" ]; then
            log "Core reproducibility: MATCH ($hash1)"
        else
            log "Core reproducibility: DIFFER (expected — different compilation paths)"
            log "  Core1: $hash1"
            log "  Core2: $hash2"
        fi
    fi

    echo ""
    log "Core2 built successfully"
    echo ""
}

# ============================================================================
# Step 4: Full1 — Core2 compiles the full compiler
# ============================================================================

step4_full1() {
    log "================================================================"
    log "Step 4: Full1 (Core2 compiles full compiler)"
    log "================================================================"
    echo ""

    run "$BUILD_DIR/core2" compile src/app/cli/main.spl -o "$BUILD_DIR/full1"

    if [ ! -f "$BUILD_DIR/full1" ]; then
        err "Full1 binary not created"
        exit 1
    fi

    chmod +x "$BUILD_DIR/full1"

    local bin_size
    bin_size=$(wc -c < "$BUILD_DIR/full1")
    log "Full1 binary: $bin_size bytes"

    # Smoke test
    if run "$BUILD_DIR/full1" --version >/dev/null 2>&1; then
        log "Smoke test: $("$BUILD_DIR/full1" --version 2>/dev/null | head -1)"
    fi

    echo ""
    log "Full1 built successfully"
    echo ""
}

# ============================================================================
# Step 5: Full2 — Full1 recompiles itself (reproducibility)
# ============================================================================

step5_full2() {
    if [ "$SKIP_VERIFY" = true ]; then
        log "Skipping Full2 (--skip-verify)"
        echo ""
        return
    fi

    log "================================================================"
    log "Step 5: Full2 (Full1 recompiles itself — reproducibility check)"
    log "================================================================"
    echo ""

    run "$BUILD_DIR/full1" compile src/app/cli/main.spl -o "$BUILD_DIR/full2"

    if [ ! -f "$BUILD_DIR/full2" ]; then
        err "Full2 binary not created"
        exit 1
    fi

    chmod +x "$BUILD_DIR/full2"

    local bin_size
    bin_size=$(wc -c < "$BUILD_DIR/full2")
    log "Full2 binary: $bin_size bytes"

    local hash1 hash2
    hash1=$(file_hash "$BUILD_DIR/full1")
    hash2=$(file_hash "$BUILD_DIR/full2")
    if [ "$hash1" = "$hash2" ]; then
        log "Full reproducibility: MATCH ($hash1)"
    else
        err "Full reproducibility: MISMATCH"
        err "  Full1: $hash1"
        err "  Full2: $hash2"
        exit 1
    fi

    echo ""
    log "Reproducibility verified"
    echo ""
}

# ============================================================================
# Step 6: Install
# ============================================================================

step6_install() {
    log "================================================================"
    log "Step 6: Install"
    log "================================================================"
    echo ""

    local src
    if [ -f "$BUILD_DIR/full2" ]; then
        src="$BUILD_DIR/full2"
    else
        src="$BUILD_DIR/full1"
    fi

    mkdir -p "$(dirname "$OUTPUT")"
    cp "$src" "$OUTPUT"
    chmod +x "$OUTPUT"
    log "Installed: $OUTPUT ($(wc -c < "$OUTPUT") bytes)"

    echo ""
}

# ============================================================================
# Cleanup
# ============================================================================

cleanup() {
    if [ "$KEEP_ARTIFACTS" = false ]; then
        log "Cleaning up $BUILD_DIR..."
        rm -rf "$BUILD_DIR"
    else
        log "Artifacts kept in $BUILD_DIR/"
        ls -la "$BUILD_DIR/"
    fi
    echo ""
}

# ============================================================================
# Main
# ============================================================================

main() {
    local start_time
    start_time=$(date +%s)

    echo "================================================================"
    echo "  Simple Compiler — Bootstrap From Scratch"
    echo "================================================================"
    echo ""

    step0_prerequisites
    step1_build_seed
    step2_core1
    step3_core2
    step4_full1
    step5_full2
    step6_install
    cleanup

    local end_time elapsed
    end_time=$(date +%s)
    elapsed=$((end_time - start_time))

    echo "================================================================"
    echo "  Bootstrap Complete (${elapsed}s)"
    echo "================================================================"
    echo ""
    echo "  Binary: $OUTPUT"
    echo "  Usage:  $OUTPUT <command>"
    echo ""
    echo "  Try:    $OUTPUT --version"
    echo "          $OUTPUT test"
    echo "          $OUTPUT build"
    echo ""
}

main "$@"
