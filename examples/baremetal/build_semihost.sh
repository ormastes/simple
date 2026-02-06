#!/bin/bash
# Build RISC-V 32 Semihosting Binary with LLVM or GCC
#
# Supports:
#   - LLVM/Clang (preferred - works for all architectures)
#   - GCC RISC-V toolchain (fallback)
#
# Install LLVM:
#   Ubuntu: sudo apt install clang-16 lld-16
#   macOS:  brew install llvm
#   Windows: choco install llvm
#
# Install GCC (fallback):
#   sudo apt install gcc-riscv64-unknown-elf

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

echo "╔════════════════════════════════════════════════════════════════╗"
echo "║  Building RISC-V 32 Semihosting Binary                        ║"
echo "╚════════════════════════════════════════════════════════════════╝"
echo ""

# Detect toolchain
TOOLCHAIN=""
ASSEMBLER=""
LINKER=""

# Try LLVM first (preferred)
if command -v clang-16 &> /dev/null && command -v lld-16 &> /dev/null; then
    TOOLCHAIN="LLVM"
    ASSEMBLER="clang-16"
    LINKER="lld-16"
    echo "✓ Using LLVM toolchain (clang-16 + lld-16)"
elif command -v clang &> /dev/null && command -v lld &> /dev/null; then
    TOOLCHAIN="LLVM"
    ASSEMBLER="clang"
    LINKER="lld"
    echo "✓ Using LLVM toolchain (clang + lld)"
# Try GCC fallback
elif command -v riscv64-unknown-elf-as &> /dev/null && command -v riscv64-unknown-elf-ld &> /dev/null; then
    TOOLCHAIN="GCC"
    ASSEMBLER="riscv64-unknown-elf-as"
    LINKER="riscv64-unknown-elf-ld"
    echo "✓ Using GCC RISC-V toolchain (riscv64-unknown-elf)"
else
    echo "❌ Error: No suitable toolchain found"
    echo ""
    echo "Install LLVM (recommended):"
    echo "  Ubuntu: sudo apt install clang-16 lld-16"
    echo "  macOS:  brew install llvm"
    echo ""
    echo "Or install GCC RISC-V (fallback):"
    echo "  sudo apt install gcc-riscv64-unknown-elf"
    echo ""
    exit 1
fi

echo ""

# Build with LLVM
if [ "$TOOLCHAIN" = "LLVM" ]; then
    echo "→ Compiling hello_riscv32_semihost.s with LLVM..."

    # LLVM can compile assembly directly to ELF
    $ASSEMBLER \
        -target riscv32-unknown-none \
        -march=rv32i \
        -mabi=ilp32 \
        -nostdlib \
        -static \
        -Wl,-Ttext=0x80000000 \
        -Wl,--no-relax \
        -fuse-ld=lld \
        hello_riscv32_semihost.s \
        -o hello_riscv32_semihost.elf

    # Alternative: Two-step (assemble + link)
    # $ASSEMBLER -target riscv32-unknown-none -march=rv32i -c hello_riscv32_semihost.s -o /tmp/hello.o
    # $LINKER -flavor gnu -m elf32lriscv /tmp/hello.o -o hello_riscv32_semihost.elf -Ttext=0x80000000

# Build with GCC
elif [ "$TOOLCHAIN" = "GCC" ]; then
    echo "→ Assembling hello_riscv32_semihost.s with GCC..."
    $ASSEMBLER \
        -march=rv32i \
        -mabi=ilp32 \
        hello_riscv32_semihost.s \
        -o /tmp/hello_riscv32_semihost.o

    echo "→ Linking hello_riscv32_semihost.elf with GCC..."
    $LINKER \
        -m elf32lriscv \
        /tmp/hello_riscv32_semihost.o \
        -o hello_riscv32_semihost.elf \
        -Ttext=0x80000000 \
        --no-relax
fi

# Check result
if [ -f hello_riscv32_semihost.elf ]; then
    SIZE=$(du -h hello_riscv32_semihost.elf | cut -f1)
    echo ""
    echo "✓ Built: hello_riscv32_semihost.elf ($SIZE)"
    echo "✓ Toolchain: $TOOLCHAIN"
    echo ""

    # Show some info
    if command -v file &> /dev/null; then
        file hello_riscv32_semihost.elf
    fi

    # Test with QEMU
    echo ""
    echo "Testing with QEMU..."
    if command -v qemu-system-riscv32 &> /dev/null; then
        echo "→ Running in QEMU..."
        timeout 5 qemu-system-riscv32 \
            -M virt \
            -bios none \
            -kernel hello_riscv32_semihost.elf \
            -nographic \
            -semihosting-config enable=on,target=native \
            2>&1 || true
        echo ""
        echo "✓ QEMU test complete"
    elif [ -f ../../resources/qemu/bin/qemu-system-riscv32 ]; then
        echo "→ Running with project QEMU..."
        timeout 5 ../../resources/qemu/bin/qemu-system-riscv32 \
            -M virt \
            -bios none \
            -kernel hello_riscv32_semihost.elf \
            -nographic \
            -semihosting-config enable=on,target=native \
            2>&1 || true
        echo ""
        echo "✓ QEMU test complete"
    else
        echo "⚠ qemu-system-riscv32 not found, skipping test"
    fi
else
    echo "❌ Build failed"
    exit 1
fi

echo ""
echo "╔════════════════════════════════════════════════════════════════╗"
echo "║  Build Complete with $TOOLCHAIN!                              "
echo "╚════════════════════════════════════════════════════════════════╝"
