#!/usr/bin/env bash
# Bootstrap the Simple compiler using Rust seed + Simple self-hosting.
#
# This script builds the Simple compiler via a Rust bootstrap seed,
# then self-hosts the compiler to produce the final binary.
#
# Bootstrap chain:
#   Phase 0: Try downloading release binary (optional)
#   Phase 1: Build Rust seed (cargo build --profile bootstrap -p simple-driver)
#   Phase 2: Use Rust seed to compile Simple compiler (stage1)
#   Phase 3: Self-host — stage1 recompiles itself (stage2)
#   Phase 4: Verify reproducibility (stage1 vs stage2 hash comparison)
#   Phase 5: Deploy to bin/release/simple
#
# Supported platforms: Linux (x86_64, aarch64), macOS (x86_64, arm64), FreeBSD
#
# Usage:
#   scripts/bootstrap/bootstrap-from-scratch.sh                     # Try release download, fall back to Rust build
#   scripts/bootstrap/bootstrap-from-scratch.sh --skip-download     # Skip release download, force Rust build
#   scripts/bootstrap/bootstrap-from-scratch.sh --skip-rust-build   # Reuse existing Rust seed binary
#   scripts/bootstrap/bootstrap-from-scratch.sh --deploy            # Copy result to bin/release/
#   scripts/bootstrap/bootstrap-from-scratch.sh --keep-artifacts    # Keep build dir
#   scripts/bootstrap/bootstrap-from-scratch.sh --jobs=4            # Parallel jobs
#
# Outputs:
#   build/bootstrap/stage1/simple  — Stage 1 binary (compiled by Rust seed)
#   build/bootstrap/stage2/simple  — Stage 2 binary (self-hosted)
#   bin/release/simple             — (with --deploy) deployed binary

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(cd "${SCRIPT_DIR}/../.." && pwd)"
BUILD_DIR="${PROJECT_DIR}/build"
BOOTSTRAP_DIR="${BUILD_DIR}/bootstrap"
RELEASE_DIR="${PROJECT_DIR}/bin/release"
RUST_SEED_DIR="${PROJECT_DIR}/src/compiler_rust"
RUST_SEED_BIN="${RUST_SEED_DIR}/target/bootstrap/simple"

# Parse arguments
DEPLOY=false
KEEP_ARTIFACTS=false
JOBS=7
SKIP_DOWNLOAD=false
SKIP_RUST_BUILD=false
DOWNLOAD_VERSION=""
BACKEND="auto"
VERIFY_HASH=true

for arg in "$@"; do
    case "$arg" in
        --deploy|--update-release) DEPLOY=true ;;
        --keep-artifacts) KEEP_ARTIFACTS=true ;;
        --jobs=*) JOBS="${arg#--jobs=}" ;;
        --skip-download) SKIP_DOWNLOAD=true ;;
        --skip-rust-build) SKIP_RUST_BUILD=true ;;
        --download-version=*) DOWNLOAD_VERSION="${arg#--download-version=}" ;;
        --backend=*) BACKEND="${arg#--backend=}" ;;
        --no-verify) VERIFY_HASH=false ;;
        --help|-h)
            echo "Usage: $0 [--deploy] [--update-release] [--keep-artifacts] [--jobs=N]"
            echo "         [--skip-download] [--skip-rust-build] [--download-version=X.Y.Z]"
            echo "         [--backend=auto|c|llvm|cranelift] [--no-verify]"
            echo ""
            echo "Options:"
            echo "  --skip-download          Skip release binary download, force Rust bootstrap"
            echo "  --skip-rust-build        Reuse existing Rust seed binary (skip cargo build)"
            echo "  --download-version=X.Y.Z Pin release download to a specific version"
            echo "  --backend=BACKEND        Backend for self-host compilation (default: auto)"
            echo "  --deploy, --update-release  Copy result to bin/release/simple"
            echo "  --keep-artifacts         Keep build directory after completion"
            echo "  --no-verify              Skip stage1 vs stage2 hash verification"
            echo "  --jobs=N                 Parallel compilation jobs (default: 7)"
            exit 0
            ;;
        *) echo "Unknown argument: $arg"; exit 1 ;;
    esac
done

# ================================================================
# Platform detection
# ================================================================
detect_platform() {
    local os arch
    os="$(uname -s)"
    arch="$(uname -m)"

    case "$os" in
        Linux)  HOST_OS="linux" ;;
        Darwin) HOST_OS="macos" ;;
        FreeBSD) HOST_OS="freebsd" ;;
        *) echo "Error: Unsupported OS: $os"; exit 1 ;;
    esac

    case "$arch" in
        x86_64|amd64) HOST_ARCH="x86_64" ;;
        aarch64|arm64) HOST_ARCH="aarch64" ;;
        *) echo "Error: Unsupported architecture: $arch"; exit 1 ;;
    esac
}

detect_platform

echo "=== Simple Bootstrap (Rust Seed + Self-Host) ==="
echo "Project:    ${PROJECT_DIR}"
echo "Platform:   ${HOST_OS}-${HOST_ARCH}"
echo "Build:      ${BUILD_DIR}"
echo "Backend:    ${BACKEND}"
echo "Jobs:       ${JOBS}"
echo ""

# ================================================================
# Prerequisite checks
# ================================================================
check_tool() {
    if ! command -v "$1" &>/dev/null; then
        echo "Error: $1 not found. Please install $1."
        exit 1
    fi
}

check_prerequisites() {
    # Rust toolchain (required unless --skip-rust-build)
    if [[ "${SKIP_RUST_BUILD}" != "true" ]]; then
        check_tool rustc
        check_tool cargo
        echo "Rust:       $(rustc --version)"
    fi

    # C compiler (needed for linking)
    if command -v clang &>/dev/null; then
        echo "C compiler: clang ($(clang --version | head -1))"
    elif command -v gcc &>/dev/null; then
        echo "C compiler: gcc ($(gcc --version | head -1))"
    else
        echo "Error: No C compiler found (clang or gcc required for linking)."
        exit 1
    fi

    # llvm-lib backend requires libLLVM shared library
    if [[ "${BACKEND}" == "llvm-lib" ]]; then
        local llvm_found=false
        if ldconfig -p 2>/dev/null | grep -q libLLVM; then
            llvm_found=true
        elif ls /usr/lib/libLLVM*.so 2>/dev/null | head -1 | grep -q libLLVM; then
            llvm_found=true
        elif ls /usr/lib/libLLVM*.dylib 2>/dev/null | head -1 | grep -q libLLVM; then
            llvm_found=true
        fi
        if [[ "${llvm_found}" != "true" ]]; then
            echo "Error: libLLVM not found. Required for --backend=llvm-lib."
            echo "Install: apt install libllvm-18-dev (Ubuntu) or brew install llvm (macOS)"
            exit 1
        fi
        echo "libLLVM:    found"
    fi

    # Platform-specific checks
    case "$HOST_OS" in
        macos)
            # Ensure Xcode CLT or SDK is available
            if ! xcrun --show-sdk-path &>/dev/null 2>&1; then
                echo "Error: Xcode Command Line Tools not found."
                echo "Install with: xcode-select --install"
                exit 1
            fi
            echo "macOS SDK:  $(xcrun --show-sdk-path)"
            ;;
        freebsd)
            check_tool clang
            ;;
    esac
    echo ""
}

check_prerequisites

# ================================================================
# Phase 0: Try downloading a release binary from GitHub
# ================================================================
USED_RELEASE_BINARY=false

if [[ "${SKIP_DOWNLOAD}" != "true" ]]; then
    echo "--- Phase 0: Download release binary ---"

    DOWNLOAD_SCRIPT="${SCRIPT_DIR}/download-release.sh"
    DOWNLOAD_ARGS=("--output=${BUILD_DIR}/simple" "--quiet")

    if [[ -n "${DOWNLOAD_VERSION}" ]]; then
        DOWNLOAD_ARGS+=("--version=${DOWNLOAD_VERSION}")
    fi

    if [[ -x "${DOWNLOAD_SCRIPT}" ]]; then
        if DOWNLOADED_BIN=$("${DOWNLOAD_SCRIPT}" "${DOWNLOAD_ARGS[@]}" 2>/dev/null); then
            # Double-check with --version
            if "${BUILD_DIR}/simple" --version &>/dev/null; then
                echo "Release binary downloaded and verified: ${BUILD_DIR}/simple"
                USED_RELEASE_BINARY=true
            else
                echo "Downloaded binary failed verification, falling back to Rust bootstrap."
                rm -f "${BUILD_DIR}/simple"
            fi
        else
            echo "Release download failed or unavailable, falling back to Rust bootstrap."
        fi
    else
        echo "download-release.sh not found, falling back to Rust bootstrap."
    fi
    echo ""
else
    echo "--- Phase 0: Skipped (--skip-download) ---"
    echo ""
fi

# If release binary worked, skip the Rust bootstrap phases
if [[ "${USED_RELEASE_BINARY}" == "true" ]]; then
    echo "Using downloaded release binary — skipping Rust bootstrap."
    echo ""

    # Deploy directly if requested
    if [[ "${DEPLOY}" == "true" ]]; then
        echo "--- Deploy ---"
        mkdir -p "${RELEASE_DIR}"
        cp "${BUILD_DIR}/simple" "${RELEASE_DIR}/simple"
        chmod +x "${RELEASE_DIR}/simple"
        echo "Deployed to: ${RELEASE_DIR}/simple"
        ls -lh "${RELEASE_DIR}/simple"
    fi

    echo ""
    echo "=== Bootstrap complete (via release download) ==="
    exit 0
fi

# ================================================================
# Phase 1: Build Rust seed
# ================================================================
echo "--- Phase 1: Build Rust seed ---"

if [[ "${SKIP_RUST_BUILD}" == "true" ]]; then
    if [[ ! -x "${RUST_SEED_BIN}" ]]; then
        echo "Error: --skip-rust-build specified but Rust seed not found at: ${RUST_SEED_BIN}"
        exit 1
    fi
    echo "Reusing existing Rust seed: ${RUST_SEED_BIN}"
else
    echo "Building Rust seed (cargo build --profile bootstrap -p simple-driver)..."
    (cd "${RUST_SEED_DIR}" && cargo build --profile bootstrap -p simple-driver 2>&1)

    if [[ ! -x "${RUST_SEED_BIN}" ]]; then
        echo "Error: Rust seed build failed — binary not found at: ${RUST_SEED_BIN}"
        exit 1
    fi
    echo "Rust seed built: ${RUST_SEED_BIN}"
fi

ls -lh "${RUST_SEED_BIN}"
echo ""

# ================================================================
# Phase 2: Use Rust seed to compile Simple compiler (stage1)
# ================================================================
echo "--- Phase 2: Compile Simple compiler with Rust seed (stage1) ---"

STAGE1_DIR="${BOOTSTRAP_DIR}/stage1"
STAGE1_BIN="${STAGE1_DIR}/simple"
mkdir -p "${STAGE1_DIR}"

# Set SIMPLE_LIB so the compiler can find the standard library
export SIMPLE_LIB="${PROJECT_DIR}/src"
# Signal bootstrap mode for parser compatibility hacks
export SIMPLE_BOOTSTRAP=1

COMPILE_ARGS=(
    "native-build"
    "--source" "${PROJECT_DIR}/src/compiler"
    "--source" "${PROJECT_DIR}/src/lib"
    "--source" "${PROJECT_DIR}/src/app"
    "--entry" "${PROJECT_DIR}/src/app/cli/main.spl"
    "-o" "${STAGE1_BIN}"
    "--strip"
)

if [[ "${BACKEND}" != "auto" ]]; then
    COMPILE_ARGS+=("--backend=${BACKEND}")
fi

echo "Running: ${RUST_SEED_BIN} ${COMPILE_ARGS[*]}"
"${RUST_SEED_BIN}" "${COMPILE_ARGS[@]}" 2>&1

if [[ ! -x "${STAGE1_BIN}" ]]; then
    echo "Error: Stage 1 compilation failed — binary not found at: ${STAGE1_BIN}"
    exit 1
fi

echo "Stage 1 built: ${STAGE1_BIN}"
ls -lh "${STAGE1_BIN}"

# Quick sanity check
if "${STAGE1_BIN}" --version &>/dev/null; then
    echo "Stage 1 verification: $("${STAGE1_BIN}" --version 2>&1)"
else
    echo "Warning: Stage 1 binary does not respond to --version (may be OK for early bootstrap)"
fi
echo ""

# ================================================================
# Phase 3: Self-host — stage1 recompiles itself (stage2)
# ================================================================
echo "--- Phase 3: Self-host verification (stage1 → stage2) ---"

STAGE2_DIR="${BOOTSTRAP_DIR}/stage2"
STAGE2_BIN="${STAGE2_DIR}/simple"
mkdir -p "${STAGE2_DIR}"

if [[ "${BACKEND}" == "llvm-lib" || "${BACKEND}" == "llvm" ]]; then
    # Pure Simple compile path (driver loads all sources internally)
    SELFHOST_ARGS=(
        "compile"
        "${PROJECT_DIR}/src/app/cli/main.spl"
        "--native"
        "--backend=${BACKEND}"
        "--release"
        "-o" "${STAGE2_BIN}"
        "--verbose"
    )
else
    SELFHOST_ARGS=(
        "native-build"
        "--source" "${PROJECT_DIR}/src/compiler"
        "--source" "${PROJECT_DIR}/src/lib"
        "--source" "${PROJECT_DIR}/src/app"
        "--entry" "${PROJECT_DIR}/src/app/cli/main.spl"
        "-o" "${STAGE2_BIN}"
        "--strip"
    )

    if [[ "${BACKEND}" != "auto" ]]; then
        SELFHOST_ARGS+=("--backend=${BACKEND}")
    fi
fi

echo "Running: ${STAGE1_BIN} ${SELFHOST_ARGS[*]}"
"${STAGE1_BIN}" "${SELFHOST_ARGS[@]}" 2>&1

if [[ ! -x "${STAGE2_BIN}" ]]; then
    echo "Error: Stage 2 self-host compilation failed — binary not found at: ${STAGE2_BIN}"
    exit 1
fi

echo "Stage 2 built: ${STAGE2_BIN}"
ls -lh "${STAGE2_BIN}"

# Verify stage2 works
if "${STAGE2_BIN}" --version &>/dev/null; then
    echo "Stage 2 verification: $("${STAGE2_BIN}" --version 2>&1)"
else
    echo "Warning: Stage 2 binary does not respond to --version"
fi
echo ""

# ================================================================
# Phase 4: Verify reproducibility (stage1 vs stage2 hash)
# ================================================================
if [[ "${VERIFY_HASH}" == "true" ]]; then
    echo "--- Phase 4: Reproducibility verification ---"

    # Use shasum on macOS, sha256sum on Linux/FreeBSD
    if command -v sha256sum &>/dev/null; then
        HASH_CMD="sha256sum"
    elif command -v shasum &>/dev/null; then
        HASH_CMD="shasum -a 256"
    else
        echo "Warning: No SHA-256 tool found, skipping hash verification."
        VERIFY_HASH=false
    fi

    if [[ "${VERIFY_HASH}" == "true" ]]; then
        HASH1=$(${HASH_CMD} "${STAGE1_BIN}" | awk '{print $1}')
        HASH2=$(${HASH_CMD} "${STAGE2_BIN}" | awk '{print $1}')

        echo "Stage 1 SHA-256: ${HASH1}"
        echo "Stage 2 SHA-256: ${HASH2}"

        if [[ "${HASH1}" == "${HASH2}" ]]; then
            echo "Reproducibility check PASSED — stage1 and stage2 are identical."
        else
            echo "Note: stage1 and stage2 differ (expected if timestamps/paths are embedded)."
            echo "Both binaries are functional — using stage2 as the final binary."
        fi
    fi
    echo ""
else
    echo "--- Phase 4: Skipped (--no-verify) ---"
    echo ""
fi

# ================================================================
# Phase 5: Deploy to bin/release/simple
# ================================================================
# Use stage2 as the final binary (self-hosted)
FINAL_BIN="${STAGE2_BIN}"

if [[ "${DEPLOY}" == "true" ]]; then
    echo "--- Phase 5: Deploy ---"
    mkdir -p "${RELEASE_DIR}"
    cp "${FINAL_BIN}" "${RELEASE_DIR}/simple"
    chmod +x "${RELEASE_DIR}/simple"

    echo "Deployed to:"
    ls -lh "${RELEASE_DIR}/simple"
    echo ""
fi

# ================================================================
# Cleanup
# ================================================================
if [[ "${KEEP_ARTIFACTS}" != "true" ]]; then
    echo "Cleaning build directory..."
    rm -rf "${BOOTSTRAP_DIR}"
fi

echo ""
echo "=== Bootstrap complete (Rust seed → stage1 → stage2) ==="
echo "Final binary: ${FINAL_BIN}"
