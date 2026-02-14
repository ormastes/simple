#!/bin/bash
# Verify Bare-Metal Build System Setup
#
# Checks that all infrastructure is in place for bare-metal builds.

set -e

echo "=== Bare-Metal Build System Verification ==="
echo ""

# Color codes
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

check_file() {
    if [ -f "$1" ]; then
        echo -e "${GREEN}✓${NC} $1"
        return 0
    else
        echo -e "${RED}✗${NC} $1 (missing)"
        return 1
    fi
}

check_executable() {
    if command -v "$1" &> /dev/null; then
        VERSION=$($1 --version 2>&1 | head -1)
        echo -e "${GREEN}✓${NC} $1 (${VERSION})"
        return 0
    else
        echo -e "${YELLOW}⚠${NC} $1 (not installed - required for $2)"
        return 1
    fi
}

ERRORS=0

# Check linker scripts
echo "Linker Scripts:"
check_file "src/compiler/baremetal/arm/linker.ld" || ERRORS=$((ERRORS+1))
check_file "src/compiler/baremetal/x86_64/linker.ld" || ERRORS=$((ERRORS+1))
check_file "src/compiler/baremetal/riscv/linker.ld" || ERRORS=$((ERRORS+1))
echo ""

# Check startup code
echo "Startup Code (crt0.s):"
check_file "src/compiler/baremetal/arm/crt0.s" || ERRORS=$((ERRORS+1))
check_file "src/compiler/baremetal/x86_64/crt0.s" || ERRORS=$((ERRORS+1))
check_file "src/compiler/baremetal/riscv/crt0.s" || ERRORS=$((ERRORS+1))
echo ""

# Check build system files
echo "Build System:"
check_file "src/app/build/baremetal.spl" || ERRORS=$((ERRORS+1))
check_file "src/app/build/main.spl" || ERRORS=$((ERRORS+1))
check_file "src/app/build/types.spl" || ERRORS=$((ERRORS+1))
echo ""

# Check tests
echo "Tests:"
check_file "test/integration/baremetal_build_spec.spl" || ERRORS=$((ERRORS+1))
echo ""

# Check documentation
echo "Documentation:"
check_file "doc/guide/baremetal_quick_start.md" || ERRORS=$((ERRORS+1))
check_file "doc/report/baremetal_build_system_integration_2026-02-14.md" || ERRORS=$((ERRORS+1))
echo ""

# Check toolchains (optional)
echo "Toolchains (optional - required for actual builds):"
check_executable "arm-none-eabi-as" "ARM builds"
check_executable "arm-none-eabi-ld" "ARM builds"
check_executable "qemu-system-arm" "ARM testing"
echo ""
check_executable "as" "x86_64 builds"
check_executable "ld" "x86_64 builds"
check_executable "qemu-system-x86_64" "x86_64 testing"
echo ""
check_executable "riscv64-unknown-elf-as" "RISC-V builds" || \
    check_executable "riscv64-linux-gnu-as" "RISC-V builds"
check_executable "riscv64-unknown-elf-ld" "RISC-V builds" || \
    check_executable "riscv64-linux-gnu-ld" "RISC-V builds"
check_executable "qemu-system-riscv64" "RISC-V testing"
echo ""

# Summary
echo "=== Summary ==="
if [ $ERRORS -eq 0 ]; then
    echo -e "${GREEN}All infrastructure files present!${NC}"
    echo ""
    echo "Next steps:"
    echo "  1. Implement compiler backend for bare-metal targets"
    echo "  2. Run: simple build baremetal --list-targets"
    echo "  3. Build: simple build baremetal --target=x86_64 hello.spl"
    echo ""
    exit 0
else
    echo -e "${RED}$ERRORS file(s) missing!${NC}"
    echo ""
    echo "Please ensure all infrastructure files are in place."
    exit 1
fi
