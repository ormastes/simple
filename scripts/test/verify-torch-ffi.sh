#!/usr/bin/env bash
# Verify PyTorch FFI Integration Status
# Checks FFI library, runtime, and integration state

set -e

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Get project root
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

echo "PyTorch FFI Integration Verification"
echo "====================================="
echo ""

# Check 1: FFI library exists
echo -n "1. FFI library exists: "
FFI_LIB="$PROJECT_ROOT/.build/rust/ffi_torch/target/release/libsimple_torch_ffi.so"
if [ -f "$FFI_LIB" ]; then
    SIZE=$(ls -lh "$FFI_LIB" | awk '{print $5}')
    echo -e "${GREEN}✓${NC} ($SIZE)"
else
    echo -e "${RED}✗${NC} Not found at: $FFI_LIB"
    exit 1
fi

# Check 2: FFI library has exported symbols
echo -n "2. FFI library exports rt_torch_available: "
if nm -D "$FFI_LIB" 2>/dev/null | grep -q "T rt_torch_available"; then
    echo -e "${GREEN}✓${NC}"
else
    echo -e "${RED}✗${NC}"
    exit 1
fi

# Check 3: Count exported symbols
echo -n "3. FFI library symbol count: "
SYMBOL_COUNT=$(nm -D "$FFI_LIB" 2>/dev/null | grep " T rt_torch" | wc -l)
echo "$SYMBOL_COUNT functions"

# Check 4: Runtime binary exists
echo -n "4. Runtime binary exists: "
RUNTIME="$PROJECT_ROOT/bin/release/simple"
if [ -f "$RUNTIME" ]; then
    SIZE=$(ls -lh "$RUNTIME" | awk '{print $5}')
    echo -e "${GREEN}✓${NC} ($SIZE)"
else
    echo -e "${RED}✗${NC} Not found at: $RUNTIME"
    exit 1
fi

# Check 5: Runtime has torch symbols
echo -n "5. Runtime has rt_torch_tensor_zeros: "
if nm "$RUNTIME" 2>/dev/null | grep -q " T rt_torch_tensor_zeros"; then
    echo -e "${GREEN}✓ INTEGRATED${NC}"
    INTEGRATED=true
else
    echo -e "${YELLOW}✗ NOT INTEGRATED${NC}"
    INTEGRATED=false
fi

# Check 6: Runtime has JIT symbols
echo -n "6. Runtime has rt_torch_jit_forward: "
if nm "$RUNTIME" 2>/dev/null | grep -q " T rt_torch_jit_forward"; then
    echo -e "${GREEN}✓${NC}"
else
    echo -e "${YELLOW}✗${NC}"
fi

# Check 7: Simple API files exist
echo -n "7. Simple API files exist: "
if [ -f "$PROJECT_ROOT/src/lib/torch/mod.spl" ] && [ -f "$PROJECT_ROOT/src/lib/torch/ffi.spl" ]; then
    echo -e "${GREEN}✓${NC}"
else
    echo -e "${RED}✗${NC}"
    exit 1
fi

# Check 8: Example files exist
echo -n "8. Example files exist (5 total): "
EXAMPLE_COUNT=$(find "$PROJECT_ROOT/examples/torch" -name "*.spl" 2>/dev/null | wc -l)
if [ "$EXAMPLE_COUNT" -eq 5 ]; then
    echo -e "${GREEN}✓${NC}"
else
    echo -e "${YELLOW}$EXAMPLE_COUNT found${NC}"
fi

# Check 9: Test suite exists
echo -n "9. Test suite exists: "
if [ -f "$PROJECT_ROOT/test/system/dl_examples_system_spec.spl" ]; then
    echo -e "${GREEN}✓${NC}"
else
    echo -e "${RED}✗${NC}"
fi

# Check 10: Documentation exists
echo -n "10. Documentation exists: "
if [ -f "$PROJECT_ROOT/doc/torch_ffi_integration.md" ]; then
    echo -e "${GREEN}✓${NC}"
else
    echo -e "${RED}✗${NC}"
fi

echo ""
echo "====================================="

# Summary
if [ "$INTEGRATED" = true ]; then
    echo -e "${GREEN}STATUS: PyTorch FFI is INTEGRATED${NC}"
    echo ""
    echo "You can run PyTorch examples:"
    echo "  bin/simple examples/torch/basics/01_tensor_creation.spl"
else
    echo -e "${YELLOW}STATUS: PyTorch FFI is NOT INTEGRATED${NC}"
    echo ""
    echo "The FFI library is built but not linked into the runtime."
    echo ""
    echo "To integrate:"
    echo "  1. Modify seed build to link: -lsimple_torch_ffi"
    echo "  2. Rebuild runtime: script/install.sh"
    echo "  3. Re-run this script to verify"
    echo ""
    echo "Or use wrapper script (sets LD_LIBRARY_PATH):"
    echo "  bin/simple-torch examples/torch/basics/01_tensor_creation.spl"
    echo ""
    echo "For more details, see: doc/torch_ffi_integration.md"
fi

echo ""
echo "Test suite (works in both modes):"
echo "  bin/simple test test/system/dl_examples_system_spec.spl"
echo ""
