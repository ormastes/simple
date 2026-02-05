#!/bin/bash
# QEMU Test Runner for Simple Bare-Metal Binaries
#
# Usage:
#   ./qemu_runner.sh <binary.elf> [--timeout=30]
#
# QEMU is started with:
#   - Serial output to stdout
#   - ISA debug exit device (port 0xF4)
#   - No display
#
# Exit codes:
#   0 = Success (QEMU exit via port 0xF4 with value 0)
#   1 = Test failure
#   124 = Timeout
#   Other = QEMU error

set -e

# Default timeout in seconds
TIMEOUT=30
BINARY=""

# Parse arguments
for arg in "$@"; do
    case $arg in
        --timeout=*)
            TIMEOUT="${arg#*=}"
            ;;
        *)
            if [ -z "$BINARY" ]; then
                BINARY="$arg"
            fi
            ;;
    esac
done

if [ -z "$BINARY" ]; then
    echo "Usage: $0 <binary.elf> [--timeout=N]"
    exit 1
fi

if [ ! -f "$BINARY" ]; then
    echo "Error: Binary not found: $BINARY"
    exit 1
fi

# Detect architecture from binary
ARCH=$(file "$BINARY" 2>/dev/null | grep -oE '(x86-64|i386|ARM|RISC-V)' | head -1)

case "$ARCH" in
    "x86-64")
        QEMU="qemu-system-x86_64"
        ;;
    "i386")
        QEMU="qemu-system-i386"
        ;;
    "ARM")
        QEMU="qemu-system-arm"
        # TODO: Add ARM-specific options
        ;;
    "RISC-V")
        QEMU="qemu-system-riscv32"
        # TODO: Add RISC-V-specific options
        ;;
    *)
        # Default to i386
        QEMU="qemu-system-i386"
        ;;
esac

# Check if QEMU is available
if ! command -v "$QEMU" &> /dev/null; then
    echo "Error: $QEMU not found"
    exit 1
fi

echo "[QEMU] Running: $BINARY"
echo "[QEMU] Architecture: $ARCH"
echo "[QEMU] Timeout: ${TIMEOUT}s"
echo "[QEMU] Command: $QEMU -kernel $BINARY -serial stdio -display none -device isa-debug-exit,iobase=0xF4,iosize=0x04"
echo "----------------------------------------"

# Run QEMU with timeout
# Exit code mapping:
#   - QEMU exit code when using isa-debug-exit = (value << 1) | 1
#   - So value 0 (success) = exit code 1
#   - Value 1 (failure) = exit code 3
timeout $TIMEOUT $QEMU \
    -kernel "$BINARY" \
    -serial stdio \
    -display none \
    -device isa-debug-exit,iobase=0xF4,iosize=0x04 \
    -no-reboot \
    2>&1

QEMU_EXIT=$?

echo ""
echo "----------------------------------------"

# Map QEMU exit code
case $QEMU_EXIT in
    0)
        # QEMU exited normally (no debug exit)
        echo "[QEMU] Test completed (no exit code)"
        exit 0
        ;;
    1)
        # Debug exit with value 0 (success)
        echo "[QEMU] Test PASSED"
        exit 0
        ;;
    3)
        # Debug exit with value 1 (failure)
        echo "[QEMU] Test FAILED"
        exit 1
        ;;
    124)
        echo "[QEMU] Test TIMEOUT after ${TIMEOUT}s"
        exit 124
        ;;
    *)
        echo "[QEMU] QEMU exited with code: $QEMU_EXIT"
        exit $QEMU_EXIT
        ;;
esac
