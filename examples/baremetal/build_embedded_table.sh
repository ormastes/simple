#!/bin/bash
# Build RISC-V 32 with Embedded String Table
#
# This version embeds the string table directly in the binary's .smt section.
# No external .smt files needed - QEMU reads table from binary memory.

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

echo "╔════════════════════════════════════════════════════════════════╗"
echo "║  Building RISC-V 32 with Embedded String Table               ║"
echo "╚════════════════════════════════════════════════════════════════╝"
echo ""

# Detect toolchain
if command -v clang-16 &> /dev/null && command -v lld-16 &> /dev/null; then
    ASSEMBLER="clang-16"
    echo "✓ Using LLVM toolchain (clang-16 + lld-16)"
elif command -v clang &> /dev/null && command -v lld &> /dev/null; then
    ASSEMBLER="clang"
    echo "✓ Using LLVM toolchain (clang + lld)"
else
    echo "❌ Error: LLVM not found"
    echo "Install: sudo apt install clang-16 lld-16"
    exit 1
fi

echo ""

# Build
echo "→ Compiling hello_riscv32_embedded_table.s..."
$ASSEMBLER \
    -target riscv32-unknown-none \
    -march=rv32i \
    -mabi=ilp32 \
    -nostdlib \
    -static \
    -Wl,-Ttext=0x80000000 \
    -Wl,--no-relax \
    -fuse-ld=lld \
    hello_riscv32_embedded_table.s \
    -o hello_riscv32_embedded_table.elf

# Check result
if [ -f hello_riscv32_embedded_table.elf ]; then
    SIZE=$(du -b hello_riscv32_embedded_table.elf | cut -f1)
    SIZE_KB=$(echo "scale=1; $SIZE / 1024" | bc)
    echo ""
    echo "✓ Built: hello_riscv32_embedded_table.elf ($SIZE bytes, ${SIZE_KB}KB)"
    echo ""

    # Show sections
    if command -v llvm-objdump &> /dev/null; then
        echo "ELF Sections:"
        llvm-objdump -h hello_riscv32_embedded_table.elf | grep -E "\.text|\.smt|\.data"
        echo ""
    elif command -v riscv64-unknown-elf-objdump &> /dev/null; then
        echo "ELF Sections:"
        riscv64-unknown-elf-objdump -h hello_riscv32_embedded_table.elf | grep -E "\.text|\.smt|\.data"
        echo ""
    fi

    # Show size comparison
    if [ -f hello_riscv32_semihost.elf ]; then
        TEXT_SIZE=$(du -b hello_riscv32_semihost.elf | cut -f1)
        REDUCTION=$((100 - (SIZE * 100 / TEXT_SIZE)))
        echo "Size Comparison:"
        echo "  Text mode (embedded strings):  $TEXT_SIZE bytes"
        echo "  Embedded table (IDs only):     $SIZE bytes"
        echo "  Reduction:                     ${REDUCTION}%"
        echo ""
    fi

    # Display string table
    echo "String Table Contents:"
    if command -v llvm-objdump &> /dev/null; then
        llvm-objdump -s -j .smt hello_riscv32_embedded_table.elf 2>/dev/null || echo "  (use readelf to inspect .smt section)"
    fi

    echo ""
    echo "✓ Build complete!"
    echo ""
    echo "To test with custom QEMU:"
    echo "  resources/qemu/bin/qemu-system-riscv32-simple \\"
    echo "    -M virt -bios none \\"
    echo "    -kernel hello_riscv32_embedded_table.elf \\"
    echo "    -nographic \\"
    echo "    -semihosting-config enable=on"
else
    echo "❌ Build failed"
    exit 1
fi
