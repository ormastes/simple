#!/bin/bash
# Build MedGemma Korean training pipeline (native C binary)
#
# Usage:
#   cd <repo-root>
#   bash examples/projects/medgemma_korean/build_native.sh
#
# Output: /tmp/medgemma (executable)

set -e

REPO_ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$REPO_ROOT"

TORCH_DIR="$HOME/.local/lib/python3.12/site-packages/torch"
if [ ! -d "$TORCH_DIR" ]; then
    echo "ERROR: PyTorch not found at $TORCH_DIR"
    echo "Install: pip install torch"
    exit 1
fi

if [ ! -f "build/libspl_torch.so" ]; then
    echo "ERROR: build/libspl_torch.so not found"
    echo "Build it first: see src/runtime/torch_ffi.cpp"
    exit 1
fi

echo "Compiling medgemma_native.c..."
gcc -std=gnu11 -O2 -c -I src/runtime \
    -o /tmp/medgemma.o \
    examples/projects/medgemma_korean/medgemma_native.c

echo "Compiling runtime.c..."
gcc -std=gnu11 -O2 -c -I src/runtime \
    -o /tmp/runtime.o \
    src/runtime/runtime.c

echo "Linking..."
g++ -o /tmp/medgemma /tmp/medgemma.o /tmp/runtime.o \
    -L build -lspl_torch \
    -L "$TORCH_DIR/lib" -ltorch -ltorch_cpu -lc10 \
    -Wl,-rpath,"$REPO_ROOT/build" \
    -Wl,-rpath,"$TORCH_DIR/lib" \
    -lm -lpthread -ldl

rm -f /tmp/medgemma.o /tmp/runtime.o
echo "Built: /tmp/medgemma"
echo "Run:   /tmp/medgemma"
