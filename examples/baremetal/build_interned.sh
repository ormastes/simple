#!/bin/bash
# Build RISC-V 32 Interned Semihosting Binary with LLVM
#
# This builds the string-interned version that uses protocol for 89% size reduction.
#
# Install LLVM:
#   Ubuntu: sudo apt install clang-16 lld-16
#   macOS:  brew install llvm

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

echo "╔════════════════════════════════════════════════════════════════╗"
echo "║  Building RISC-V 32 Interned Semihosting Binary              ║"
echo "╚════════════════════════════════════════════════════════════════╝"
echo ""

# Detect toolchain (LLVM preferred)
TOOLCHAIN=""
ASSEMBLER=""

if command -v clang-16 &> /dev/null && command -v lld-16 &> /dev/null; then
    TOOLCHAIN="LLVM"
    ASSEMBLER="clang-16"
    echo "✓ Using LLVM toolchain (clang-16 + lld-16)"
elif command -v clang &> /dev/null && command -v lld &> /dev/null; then
    TOOLCHAIN="LLVM"
    ASSEMBLER="clang"
    echo "✓ Using LLVM toolchain (clang + lld)"
elif command -v riscv64-unknown-elf-as &> /dev/null; then
    echo "❌ GCC not supported for interned binaries (use LLVM)"
    exit 1
else
    echo "❌ Error: LLVM not found"
    echo ""
    echo "Install LLVM:"
    echo "  Ubuntu: sudo apt install clang-16 lld-16"
    echo "  macOS:  brew install llvm"
    exit 1
fi

echo ""

# Build with LLVM
echo "→ Compiling hello_riscv32_interned.s..."
$ASSEMBLER \
    -target riscv32-unknown-none \
    -march=rv32i \
    -mabi=ilp32 \
    -nostdlib \
    -static \
    -Wl,-Ttext=0x80000000 \
    -Wl,--no-relax \
    -fuse-ld=lld \
    hello_riscv32_interned.s \
    -o hello_riscv32_interned.elf

# Check result
if [ -f hello_riscv32_interned.elf ]; then
    SIZE=$(du -b hello_riscv32_interned.elf | cut -f1)
    SIZE_KB=$(echo "scale=1; $SIZE / 1024" | bc)
    echo ""
    echo "✓ Built: hello_riscv32_interned.elf ($SIZE bytes, ${SIZE_KB}KB)"
    echo "✓ Toolchain: $TOOLCHAIN"
    echo "✓ String table: hello_riscv32_interned.smt"
    echo ""

    # Show size comparison
    if [ -f hello_riscv32_semihost.elf ]; then
        TEXT_SIZE=$(du -b hello_riscv32_semihost.elf | cut -f1)
        REDUCTION=$((100 - (SIZE * 100 / TEXT_SIZE)))
        echo "Size Comparison:"
        echo "  Text mode:    $TEXT_SIZE bytes"
        echo "  Interned:     $SIZE bytes"
        echo "  Reduction:    ${REDUCTION}%"
        echo ""
    fi

    # Show file info
    if command -v file &> /dev/null; then
        file hello_riscv32_interned.elf
    fi

    # Test with QEMU (output will be protocol frames, not readable text)
    echo ""
    echo "Testing with QEMU..."
    if command -v qemu-system-riscv32 &> /dev/null; then
        echo "→ Running in QEMU (protocol output)..."
        echo "Note: Output is binary protocol - needs parser to decode"
        timeout 5 qemu-system-riscv32 \
            -M virt \
            -bios none \
            -kernel hello_riscv32_interned.elf \
            -nographic \
            -semihosting-config enable=on,target=native \
            2>&1 | head -20 || true
        echo ""
        echo "✓ QEMU test complete (raw protocol output shown)"
    else
        echo "⚠ qemu-system-riscv32 not found, skipping test"
    fi
else
    echo "❌ Build failed"
    exit 1
fi

echo ""
echo "╔════════════════════════════════════════════════════════════════╗"
echo "║  Build Complete - String Interning Protocol                  ║"
echo "╚════════════════════════════════════════════════════════════════╝"
echo ""
echo "Next steps:"
echo "  1. Run with protocol parser: bin/simple test test/baremetal/hello_riscv32_interned_spec.spl"
echo "  2. Parser will use .smt file to reconstruct text"
echo "  3. Verify 89% size reduction"
