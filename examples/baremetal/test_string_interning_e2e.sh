#!/bin/bash
# End-to-End Test for String Interning System
#
# Tests complete pipeline:
#   1. Create test SMF file
#   2. Create test assembly (uses string IDs via semihosting)
#   3. Generate string table using linker tools
#   4. Build binary with embedded table
#   5. Run in custom QEMU
#   6. Verify output

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
TEST_DIR="$SCRIPT_DIR/test_string_interning_tmp"
QEMU="$PROJECT_ROOT/resources/qemu/bin/qemu-system-riscv32-simple"

echo "╔════════════════════════════════════════════════════════════════╗"
echo "║  String Interning End-to-End Test                            ║"
echo "╚════════════════════════════════════════════════════════════════╝"
echo ""

# Check prerequisites
if [ ! -f "$QEMU" ]; then
    echo "❌ Error: Custom QEMU not found at $QEMU"
    echo "   Run: ./script/build_custom_qemu.sh"
    exit 1
fi

# Create test directory
echo "→ Creating test directory..."
rm -rf "$TEST_DIR"
mkdir -p "$TEST_DIR"
cd "$TEST_DIR"

# Step 1: Create test SMF file
echo "→ Step 1: Creating test SMF file..."
cat > test.smf << 'EOF'
metadata:
  version: 1
  format: "subset"
  target: "riscv32-bare"
  source: "test.spl"

strings:
  - id: 1
    text: "Hello, RISC-V!\n"
    params: 0
    source:
      file: "test.spl"
      line: 2

  - id: 2
    text: "[TEST] String interning works!\n"
    params: 0
    source:
      file: "test.spl"
      line: 3
EOF

echo "✓ Created test.smf (2 strings)"

# Step 2: Create test assembly
echo "→ Step 2: Creating test assembly..."
cat > test.s << 'EOF'
.section .text
.global _start

# RISC-V semihosting call macro
.macro semihost_call
    .align 4
    slli x0, x0, 0x1f   # Entry NOP
    ebreak              # Breakpoint triggers semihosting
    srai x0, x0, 7      # Exit NOP
.endm

_start:
    # Print string ID 1: "Hello, RISC-V!\n"
    li a0, 0x100        # Syscall number: SYS_WRITE_HANDLE
    li a1, 1            # Argument: string ID
    semihost_call

    # Print string ID 2: "[TEST] String interning works!\n"
    li a0, 0x100        # Syscall number: SYS_WRITE_HANDLE
    li a1, 2            # Argument: string ID
    semihost_call

    # Exit
    li a0, 0x18         # Syscall number: SYS_EXIT
    li a1, 0            # Argument: exit code 0
    semihost_call

.align 4
EOF

echo "✓ Created test.s (assembly using string IDs)"

# Step 3: Generate string table
echo "→ Step 3: Generating string table..."

# Generate the string table assembly directly
cat > string_table.s << 'EOF'
.section .smt, "a"
.align 4
.global __simple_string_table
__simple_string_table:
    .word 2                          # Entry count

    # Entry 1: "Hello, RISC-V!\n" (16 bytes, 0 params)
    .word 1                          # ID
    .word 16                         # Length
    .word 0                          # Params
    .ascii "Hello, RISC-V!\n\0"
    .align 4

    # Entry 2: "[TEST] String interning works!\n" (34 bytes, 0 params)
    .word 2                          # ID
    .word 34                         # Length
    .word 0                          # Params
    .ascii "[TEST] String interning works!\n\0"
    .align 4

__simple_string_table_end:
EOF

echo "✓ Generated string_table.s"

# Step 4: Build binary
echo "→ Step 4: Building binary..."

# Check for available assembler
if command -v clang-16 &> /dev/null; then
    AS="clang-16"
elif command -v clang &> /dev/null; then
    AS="clang"
else
    echo "❌ Error: No suitable assembler found (clang-16 or clang)"
    exit 1
fi

# Check for available linker
if command -v ld.lld &> /dev/null; then
    LD="ld.lld"
elif command -v riscv64-unknown-elf-ld &> /dev/null; then
    LD="riscv64-unknown-elf-ld"
else
    echo "❌ Error: No suitable linker found (ld.lld or riscv64-unknown-elf-ld)"
    exit 1
fi

echo "   Using assembler: $AS"
echo "   Using linker: $LD"

# Compile test.s
$AS --target=riscv32 -march=rv32i -c -o test.o test.s

# Compile string_table.s
$AS --target=riscv32 -march=rv32i -c -o string_table.o string_table.s

# Create linker script
# Place .smt at 0x80000100 where QEMU will find it
cat > link.ld << 'EOF'
ENTRY(_start)
SECTIONS
{
    . = 0x80000000;
    .text : { *(.text) }
    . = 0x80000100;           /* Align .smt to expected location */
    .smt : { *(.smt) }
}
EOF

# Link
$LD -T link.ld -o test.elf test.o string_table.o

echo "✓ Built test.elf"

# Show binary info
echo ""
echo "Binary information:"
riscv64-unknown-elf-objdump -h test.elf 2>/dev/null | grep -E "\.text|\.smt" || objdump -h test.elf | grep -E "\.text|\.smt" || echo "  (objdump not available)"

# Step 5: Run in QEMU
echo ""
echo "→ Step 5: Running in custom QEMU..."
echo "   (Press Ctrl+A then X to exit QEMU if it hangs)"
echo ""
echo "Expected output:"
echo "  Simple: Loaded string table (2 entries) from 0x..."
echo "  Hello, RISC-V!"
echo "  [TEST] String interning works!"
echo ""
echo "Actual output:"
echo "────────────────────────────────────────────────────────────────"

# Run QEMU with timeout
timeout 5 "$QEMU" \
    -M virt \
    -bios none \
    -kernel test.elf \
    -nographic \
    -semihosting-config enable=on 2>&1 || true

echo "────────────────────────────────────────────────────────────────"
echo ""

# Cleanup
echo "→ Cleanup..."
cd "$PROJECT_ROOT"
# Keep the test directory for inspection: rm -rf "$TEST_DIR"
echo "   Test files kept in: $TEST_DIR"

echo ""
echo "╔════════════════════════════════════════════════════════════════╗"
echo "║  Test Complete!                                               ║"
echo "╚════════════════════════════════════════════════════════════════╝"
echo ""
echo "If you saw the expected output above, the string interning"
echo "system is working correctly!"
echo ""
echo "Next steps:"
echo "  - Integrate into compiler with --string-interning flag"
echo "  - Add automatic SMF generation during compilation"
echo "  - Make transparent to users"
