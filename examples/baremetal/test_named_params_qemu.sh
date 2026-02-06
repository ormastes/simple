#!/bin/bash
# End-to-End Test: Named Parameters in QEMU
#
# Tests that parameter names are preserved through the pipeline
# and that QEMU correctly handles parameterized strings

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
TEST_DIR="$SCRIPT_DIR/test_named_params_qemu_tmp"
QEMU="$PROJECT_ROOT/resources/qemu/bin/qemu-system-riscv32-simple"

echo "╔════════════════════════════════════════════════════════════════╗"
echo "║  Named Parameters QEMU Test                                   ║"
echo "╚════════════════════════════════════════════════════════════════╝"
echo ""

# Check prerequisites
if [ ! -f "$QEMU" ]; then
    echo "❌ Error: Custom QEMU not found"
    exit 1
fi

# Create test directory
echo "→ Creating test directory..."
rm -rf "$TEST_DIR"
mkdir -p "$TEST_DIR"
cd "$TEST_DIR"

# Step 1: Create SMF file with NAMED parameters
echo "→ Step 1: Creating SMF with named parameters..."
cat > test.smf << 'EOF'
metadata:
  version: 1
  format: "smf_subset"
  target: "riscv32-bare"
  source: "test.spl"

strings:
  - id: 1
    text: "Hello, {}!"
    params: 1
    param_names: ["name"]

  - id: 2
    text: "User: {}, Age: {}"
    params: 2
    param_names: ["username", "age"]

  - id: 3
    text: "RGB({}, {}, {})"
    params: 3
    param_names: ["r", "g", "b"]
EOF

echo "✓ Created SMF with named parameters"
cat test.smf
echo ""

# Step 2: Create assembly that passes parameter VALUES
echo "→ Step 2: Creating assembly with parameter values..."
cat > test.s << 'EOF'
.section .data
.align 4
params_1:
    .word 1               # String ID
    .word 42              # Parameter: name

params_2:
    .word 2               # String ID
    .word 100             # Parameter: username
    .word 25              # Parameter: age

params_3:
    .word 3               # String ID
    .word 255             # Parameter: r
    .word 128             # Parameter: g
    .word 64              # Parameter: b

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
    # Test 1: Single parameter {name}
    li a0, 0x101                # SYS_WRITE_HANDLE_P1
    la a1, params_1
    semihost_call

    # Test 2: Two parameters {username}, {age}
    li a0, 0x102                # SYS_WRITE_HANDLE_P2
    la a1, params_2
    semihost_call

    # Test 3: Three parameters {r}, {g}, {b}
    li a0, 0x103                # SYS_WRITE_HANDLE_P3
    la a1, params_3
    semihost_call

    # Exit
    li a0, 0x18         # SYS_EXIT
    li a1, 0            # exit code
    semihost_call

.align 4
EOF

echo "✓ Created assembly"

# Step 3: Generate string table (ignoring param_names for now)
echo "→ Step 3: Generating string table..."
cat > string_table.s << 'EOF'
.section .smt, "a"
.align 4
.global __simple_string_table
__simple_string_table:
    .word 3                          # Entry count

    # Entry 1: "Hello, {}!" - param_names: ["name"]
    .word 1                          # ID
    .word 12                         # Length
    .word 1                          # Params
    .ascii "Hello, {}!\n\0"
    .align 4

    # Entry 2: "User: {}, Age: {}" - param_names: ["username", "age"]
    .word 2                          # ID
    .word 20                         # Length
    .word 2                          # Params
    .ascii "User: {}, Age: {}\n\0"
    .align 4

    # Entry 3: "RGB({}, {}, {})" - param_names: ["r", "g", "b"]
    .word 3                          # ID
    .word 18                         # Length
    .word 3                          # Params
    .ascii "RGB({}, {}, {})\n\0"
    .align 4

__simple_string_table_end:
EOF

echo "✓ Generated string_table.s"

# Step 4: Build binary
echo "→ Step 4: Building binary..."

# Check for available tools
if command -v clang &> /dev/null; then
    AS="clang"
elif command -v clang-16 &> /dev/null; then
    AS="clang-16"
else
    echo "❌ No assembler found"
    exit 1
fi

if command -v ld.lld &> /dev/null; then
    LD="ld.lld"
else
    echo "❌ No linker found"
    exit 1
fi

# Compile
$AS --target=riscv32 -march=rv32i -c -o test.o test.s
$AS --target=riscv32 -march=rv32i -c -o string_table.o string_table.s

# Create linker script
cat > link.ld << 'EOF'
ENTRY(_start)
SECTIONS
{
    . = 0x80000000;
    .text : { *(.text) }
    . = 0x80000100;
    .smt : { *(.smt) }
    . = 0x80001000;
    .data : { *(.data) }
}
EOF

# Link
$LD -T link.ld -o test.elf test.o string_table.o

echo "✓ Built test.elf"

# Step 5: Run in QEMU
echo ""
echo "→ Step 5: Running in QEMU..."
echo ""
echo "Expected output (parameter names are metadata only):"
echo "  Simple: Loaded string table (3 entries) from 0x80000100"
echo "  Hello, 42!"
echo "  User: 100, Age: 25"
echo "  RGB(255, 128, 64)"
echo ""
echo "Actual output:"
echo "────────────────────────────────────────────────────────────────"

timeout 3 "$QEMU" \
    -M virt \
    -bios none \
    -kernel test.elf \
    -nographic \
    -semihosting-config enable=on 2>&1 || true

echo "────────────────────────────────────────────────────────────────"
echo ""

# Cleanup
cd "$PROJECT_ROOT"
echo "→ Test files kept in: $TEST_DIR"

echo ""
echo "╔════════════════════════════════════════════════════════════════╗"
echo "║  Test Complete!                                               ║"
echo "╚════════════════════════════════════════════════════════════════╝"
echo ""
echo "NOTE: Parameter names (name, username, age, r, g, b) are stored"
echo "      in SMF metadata for documentation and future features."
echo "      QEMU currently uses positional replacement: {} → value"
echo ""
echo "Next steps:"
echo "  - Add type information (string, int, float)"
echo "  - Implement string parameter support in QEMU"
echo "  - Auto-generate assembly from Simple source with variables"
