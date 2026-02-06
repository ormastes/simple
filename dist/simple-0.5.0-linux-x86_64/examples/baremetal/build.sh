#!/bin/bash
# Build Script for Bare-Metal Examples
# Builds all examples that have the required cross-compilers

set -e  # Exit on error

cd "$(dirname "$0")"

echo "======================================"
echo "Building Bare-Metal Examples"
echo "======================================"
echo

# Colors for output
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m' # No Color

# Check for x86 (32-bit)
echo -n "x86 (32-bit):        "
if gcc -m32 -v 2>&1 | grep -q "Target.*i.86"; then
    echo -e "${GREEN}✓${NC} Building..."
    gcc -m32 -nostdlib -ffreestanding -T x86.ld -o hello_x86.elf hello_x86.s
    echo "                     Built: hello_x86.elf ($(du -h hello_x86.elf | cut -f1))"
else
    echo -e "${YELLOW}⚠${NC} Skipped (gcc -m32 not available)"
    echo "                     Install: sudo apt install gcc-multilib"
fi
echo

# Check for x86_64
echo -n "x86_64:              "
if gcc -m64 -v 2>&1 | grep -q "Target.*x86.64"; then
    echo -e "${GREEN}✓${NC} Building..."
    gcc -m64 -nostdlib -ffreestanding -T x86_64.ld -o hello_x86_64.elf hello_x86_64.s
    echo "                     Built: hello_x86_64.elf ($(du -h hello_x86_64.elf | cut -f1))"
else
    echo -e "${YELLOW}⚠${NC} Skipped (gcc not available)"
fi
echo

# Check for ARM Cortex-M
echo -n "ARM Cortex-M:        "
if command -v arm-none-eabi-gcc &> /dev/null; then
    echo -e "${GREEN}✓${NC} Building..."
    arm-none-eabi-gcc -mcpu=cortex-m3 -mthumb -nostdlib -T arm.ld -o hello_arm.elf hello_arm.s
    echo "                     Built: hello_arm.elf ($(du -h hello_arm.elf | cut -f1))"
else
    echo -e "${YELLOW}⚠${NC} Skipped (arm-none-eabi-gcc not available)"
    echo "                     Install: sudo apt install gcc-arm-none-eabi"
fi
echo

# Check for ARM64/AArch64
echo -n "ARM64/AArch64:       "
if command -v aarch64-linux-gnu-gcc &> /dev/null; then
    echo -e "${GREEN}✓${NC} Building..."
    aarch64-linux-gnu-gcc -nostdlib -ffreestanding -T arm64.ld -o hello_arm64.elf hello_arm64.s
    echo "                     Built: hello_arm64.elf ($(du -h hello_arm64.elf | cut -f1))"
else
    echo -e "${YELLOW}⚠${NC} Skipped (aarch64-linux-gnu-gcc not available)"
    echo "                     Install: sudo apt install gcc-aarch64-linux-gnu"
fi
echo

# Check for RISC-V 32
echo -n "RISC-V 32-bit:       "
if command -v riscv32-unknown-elf-gcc &> /dev/null; then
    echo -e "${GREEN}✓${NC} Building..."
    riscv32-unknown-elf-gcc -march=rv32imac -mabi=ilp32 -nostdlib -T riscv32.ld -o hello_riscv32.elf hello_riscv32.s
    echo "                     Built: hello_riscv32.elf ($(du -h hello_riscv32.elf | cut -f1))"
elif command -v riscv64-unknown-elf-gcc &> /dev/null; then
    echo -e "${GREEN}✓${NC} Building (using riscv64 compiler)..."
    riscv64-unknown-elf-gcc -march=rv32imac -mabi=ilp32 -nostdlib -T riscv32.ld -o hello_riscv32.elf hello_riscv32.s
    echo "                     Built: hello_riscv32.elf ($(du -h hello_riscv32.elf | cut -f1))"
else
    echo -e "${YELLOW}⚠${NC} Skipped (riscv*-unknown-elf-gcc not available)"
    echo "                     Install: sudo apt install gcc-riscv64-unknown-elf"
fi
echo

# Check for RISC-V 64
echo -n "RISC-V 64-bit:       "
if command -v riscv64-unknown-elf-gcc &> /dev/null; then
    echo -e "${GREEN}✓${NC} Building..."
    riscv64-unknown-elf-gcc -march=rv64imac -mabi=lp64 -nostdlib -T riscv64.ld -o hello_riscv64.elf hello_riscv64.s
    echo "                     Built: hello_riscv64.elf ($(du -h hello_riscv64.elf | cut -f1))"
else
    echo -e "${YELLOW}⚠${NC} Skipped (riscv64-unknown-elf-gcc not available)"
    echo "                     Install: sudo apt install gcc-riscv64-unknown-elf"
fi
echo

echo "======================================"
echo "Build Summary"
echo "======================================"
echo
ls -lh *.elf 2>/dev/null | awk '{print $9, "(" $5 ")"}'|| echo "No ELF files built"
echo

echo "To test in QEMU, run:"
echo "  qemu-system-i386 -kernel hello_x86.elf -nographic -device isa-debug-exit,iobase=0xf4,iosize=0x04"
echo "  qemu-system-x86_64 -kernel hello_x86_64.elf -nographic -device isa-debug-exit,iobase=0xf4,iosize=0x04"
echo "  qemu-system-arm -M lm3s6965evb -kernel hello_arm.elf -nographic"
echo "  qemu-system-aarch64 -M virt -cpu cortex-a57 -kernel hello_arm64.elf -nographic"
echo "  qemu-system-riscv32 -M virt -kernel hello_riscv32.elf -nographic"
echo "  qemu-system-riscv64 -M virt -kernel hello_riscv64.elf -nographic"
