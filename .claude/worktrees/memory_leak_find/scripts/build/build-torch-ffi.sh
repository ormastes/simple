#!/bin/bash
# build-torch-ffi.sh - Build libspl_torch.so from torch_ffi.cpp
#
# Usage:
#   bash scripts/build/build-torch-ffi.sh
#
# Requires:
#   - PyTorch 2.x installed (pip install torch)
#   - clang++ (or g++) with C++17 support
#   - CUDA toolkit (for GPU support)
#
# Output:
#   lib/libspl_torch.so
#
# Run tests with:
#   LD_PRELOAD=lib/libspl_torch.so bin/simple test test/unit/lib/torch_spec.spl
#
# Monitor GPU during test:
#   watch -n 0.5 nvidia-smi

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$(dirname "$SCRIPT_DIR")")"

# Detect libtorch installation path via Python
TORCH_ROOT=$(python3 -c "import torch; import os; print(os.path.dirname(torch.__file__))" 2>/dev/null) || {
    echo "ERROR: PyTorch not found. Install with: pip install torch" >&2
    exit 1
}

echo "Found libtorch at: $TORCH_ROOT"
echo "Repo root: $REPO_ROOT"

TORCH_INCLUDE_1="$TORCH_ROOT/include"
TORCH_INCLUDE_2="$TORCH_ROOT/include/torch/csrc/api/include"
TORCH_LIB="$TORCH_ROOT/lib"

# Create output directory (use build/ since repo root is read-only)
mkdir -p "$REPO_ROOT/build"

OUTPUT="$REPO_ROOT/build/libspl_torch.so"
SOURCE="$REPO_ROOT/src/runtime/torch_ffi.cpp"

if [[ ! -f "$SOURCE" ]]; then
    echo "ERROR: Source file not found: $SOURCE" >&2
    exit 1
fi

# Compiler selection: prefer clang++, fall back to g++
CXX="${CXX:-clang++}"
if ! command -v "$CXX" &>/dev/null; then
    CXX="g++"
fi

echo "Compiling with: $CXX"
echo "Output: $OUTPUT"

"$CXX" \
    -shared \
    -fPIC \
    -std=c++17 \
    -O2 \
    -I "$REPO_ROOT/src/runtime" \
    -I "$TORCH_INCLUDE_1" \
    -I "$TORCH_INCLUDE_2" \
    -L "$TORCH_LIB" \
    -Wl,-rpath,"$TORCH_LIB" \
    -ltorch \
    -ltorch_cpu \
    -ltorch_cuda \
    -lc10 \
    -lc10_cuda \
    -D_GLIBCXX_USE_CXX11_ABI=0 \
    -o "$OUTPUT" \
    "$SOURCE"

echo ""
echo "SUCCESS: Built $OUTPUT"
echo ""
echo "Run torch tests with GPU support:"
echo "  LD_PRELOAD=build/libspl_torch.so bin/simple test test/unit/lib/torch_spec.spl"
echo ""
echo "Monitor GPU during test:"
echo "  watch -n 0.5 nvidia-smi"
