#!/usr/bin/env bash
# build_llvm_simpleos_cross.sh — Configure and build a cross-clang for SimpleOS
# Requires: ormastes/llvm-project:simpleos @ b0e410881 (Phase 2 embed-LLD patches)
#
# Env vars (all optional):
#   LLVM_SRC          default: $HOME/llvm-project
#   LLVM_BUILD        default: build/os/llvm/cross-x86_64  (relative to repo root)
#   SIMPLEOS_SYSROOT  default: build/os/sysroot             (relative to repo root)
#   JOBS              default: $(nproc)
#   LLVM_BUILD_DRY_RUN=1  print commands instead of executing

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"

LLVM_SRC="${LLVM_SRC:-$HOME/llvm-project}"
LLVM_BUILD="${LLVM_BUILD:-$REPO_ROOT/build/os/llvm/cross-x86_64}"
SIMPLEOS_SYSROOT="${SIMPLEOS_SYSROOT:-$REPO_ROOT/build/os/sysroot}"
JOBS="${JOBS:-$(nproc)}"
DRY_RUN="${LLVM_BUILD_DRY_RUN:-0}"

TOOLCHAIN_FILE="$REPO_ROOT/src/os/toolchain/llvm/simpleos_cross_toolchain.cmake"
HOST_TOOLS_DIR="$(dirname "$LLVM_BUILD")/host-tools"

# --- helpers -----------------------------------------------------------------

run() {
    if [ "$DRY_RUN" = "1" ]; then
        echo "[dry-run] $*"
    else
        "$@"
    fi
}

die() { echo "error: $*" >&2; exit "${2:-1}"; }
warn() { echo "warning: $*" >&2; }

# --- 1. Verify LLVM source ---------------------------------------------------

[ -d "$LLVM_SRC" ] || die "LLVM_SRC='$LLVM_SRC' does not exist. Clone: git clone -b simpleos https://github.com/ormastes/llvm-project" 1

branch=$(git -C "$LLVM_SRC" rev-parse --abbrev-ref HEAD 2>/dev/null || echo "unknown")
if [ "$branch" != "simpleos" ]; then
    warn "LLVM_SRC is on branch '$branch', expected 'simpleos'. Continuing anyway."
fi

# --- 2. Verify sysroot -------------------------------------------------------

if [ ! -f "$SIMPLEOS_SYSROOT/lib/libsimpleos_c.a" ]; then
    echo "error: sysroot missing: $SIMPLEOS_SYSROOT/lib/libsimpleos_c.a" >&2
    echo "  Build it first:" >&2
    echo "    bin/simple run src/os/port/llvm/sysroot.shs" >&2
    exit 2
fi

# --- 3. Check host tools -----------------------------------------------------

missing_tools=()
for tool in cmake ninja clang; do
    command -v "$tool" >/dev/null 2>&1 || missing_tools+=("$tool")
done

if [ ${#missing_tools[@]} -gt 0 ]; then
    echo "error: missing host tools: ${missing_tools[*]}" >&2
    echo "  Install with:" >&2
    echo "    sudo apt-get install -y cmake ninja-build clang" >&2
    exit 3
fi

# --- 4. Note about toolchain file --------------------------------------------
# The toolchain file at src/os/toolchain/llvm/simpleos_cross_toolchain.cmake
# would cross-compile the LLVM BINARY to run INSIDE SimpleOS — that requires
# a C++ runtime on SimpleOS which we don't have yet (wave-5+). This script
# instead builds a HOST x86_64-linux clang binary that TARGETS SimpleOS via
# clang source patches (SimpleOS ToolChain class, __simpleos__ macro). No
# toolchain file needed for the binary itself.

# --- 5a. Stage host-tools (llvm-tblgen / clang-tblgen) ----------------------

if [ ! -f "$HOST_TOOLS_DIR/bin/llvm-tblgen" ]; then
    echo "==> Stage host-tools: building llvm-tblgen clang-tblgen llvm-min-tblgen"
    run mkdir -p "$HOST_TOOLS_DIR"
    run cmake -S "$LLVM_SRC/llvm" -B "$HOST_TOOLS_DIR" \
        -G Ninja \
        -DCMAKE_BUILD_TYPE=Release \
        -DLLVM_TARGETS_TO_BUILD="X86;AArch64;RISCV" \
        -DLLVM_OPTIMIZED_TABLEGEN=ON \
        -DLLVM_ENABLE_PROJECTS="clang;lld"
    run ninja -C "$HOST_TOOLS_DIR" -j"$JOBS" \
        llvm-tblgen clang-tblgen llvm-min-tblgen
else
    echo "==> Stage host-tools: already built ($HOST_TOOLS_DIR/bin/llvm-tblgen)"
fi

# --- 5b. Stage cross: cmake config -------------------------------------------
# Host x86_64-linux binary; SimpleOS appears only as a TARGET triple the
# produced clang knows how to emit code for. No CMAKE_TOOLCHAIN_FILE.

echo "==> Stage cross: cmake configure -> $LLVM_BUILD"
run mkdir -p "$LLVM_BUILD"
run cmake -S "$LLVM_SRC/llvm" -B "$LLVM_BUILD" \
    -G Ninja \
    -DCMAKE_BUILD_TYPE=Release \
    -DLLVM_TABLEGEN="$HOST_TOOLS_DIR/bin/llvm-tblgen" \
    -DCLANG_TABLEGEN="$HOST_TOOLS_DIR/bin/clang-tblgen" \
    -DLLVM_TARGETS_TO_BUILD="X86;AArch64;RISCV" \
    -DLLVM_DEFAULT_TARGET_TRIPLE=x86_64-unknown-simpleos \
    -DCLANG_DEFAULT_LINKER=lld \
    -DCLANG_SIMPLEOS_EMBED_LLD=ON \
    -DLLVM_ENABLE_PROJECTS="clang;lld"

# --- 5c. Stage cross: ninja build --------------------------------------------

echo "==> Stage cross: ninja build (this takes 30-60 min)"
run ninja -C "$LLVM_BUILD" -j"$JOBS" \
    clang lld llvm-ar llvm-nm llvm-ranlib llvm-objdump llvm-objcopy llvm-strip

# --- 6. Summary --------------------------------------------------------------

echo ""
echo "==> Done."
echo "    cross clang at $LLVM_BUILD/bin/clang"
echo "    test with:"
echo "      $LLVM_BUILD/bin/clang --target=x86_64-simpleos --sysroot=$SIMPLEOS_SYSROOT -c examples/simpleos_hello_c/hello.c -o /tmp/hello.o"
