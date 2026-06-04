#!/bin/bash
# Run semihosting test on GHDL-simulated RV32I CPU
# Usage: ./run_semihost.sh <test.s> [expected_substring]
set -e
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
RTL_DIR="$SCRIPT_DIR/../rtl"
TEST_SRC="$1"
EXPECT="${2:-}"
TEST_NAME="${TEST_SRC%.s}"
TEST_NAME="${TEST_NAME%.c}"

echo "=== Semihost Test: $TEST_SRC ==="

# Step 1: Build
EXT="${TEST_SRC##*.}"
if [ "$EXT" = "s" ]; then
    echo "[1/4] Assembling..."
    riscv64-linux-gnu-as -march=rv32i -mabi=ilp32 -o "$TEST_NAME.o" "$TEST_SRC"
    riscv64-linux-gnu-ld -m elf32lriscv -Ttext=0x80000000 --no-relax -o "$TEST_NAME.elf" "$TEST_NAME.o"
elif [ "$EXT" = "c" ]; then
    echo "[1/4] Compiling C..."
    riscv64-linux-gnu-gcc -march=rv32i -mabi=ilp32 -nostdlib -nostartfiles \
        -Wl,-Ttext=0x80000000,--no-warn-rwx-segment,--no-relax \
        -static -O2 -o "$TEST_NAME.elf" "$TEST_SRC"
fi

# Step 2: Convert to VHDL package
echo "[2/4] Generating VHDL..."
riscv64-linux-gnu-objcopy -O binary "$TEST_NAME.elf" "$TEST_NAME.bin"
python3 -c "
import struct
data = open('$TEST_NAME.bin', 'rb').read()
while len(data) % 4 != 0: data += b'\x00'
words = [struct.unpack('<I', data[i:i+4])[0] for i in range(0, len(data), 4)]
print('library ieee;')
print('use ieee.std_logic_1164.all;')
print('package test_program is')
print('    type word_array_t is array (natural range <>) of std_logic_vector(31 downto 0);')
print('    constant PROGRAM_SIZE : integer := %d;' % len(words))
print('    constant PROGRAM_DATA : word_array_t(0 to %d) := (' % (len(words)-1))
for i, w in enumerate(words):
    comma = ',' if i < len(words)-1 else ''
    print('        x\"%08x\"%s' % (w, comma))
print('    );')
print('end package test_program;')
" > "$TEST_NAME.pkg.vhd"

# Step 3: Compile + simulate (all from test dir, use absolute paths)
echo "[3/4] Compiling VHDL..."
rm -f *.cf tb_semi_run
ghdl -a --std=08 "$RTL_DIR/rv32i_pkg.vhd" "$RTL_DIR/regfile.vhd" "$RTL_DIR/alu.vhd" "$RTL_DIR/decoder.vhd" "$RTL_DIR/rv32i_core.vhd"
ghdl -a --std=08 "$TEST_NAME.pkg.vhd"
ghdl -a --std=08 "$RTL_DIR/tb_semi_run.vhd"
ghdl -e --std=08 tb_semi_run

echo "[4/4] Simulating..."
OUTPUT=$(ghdl -r --std=08 tb_semi_run --stop-time=10ms 2>&1)
echo "$OUTPUT" | grep -E "CYCLES:|EXIT_CODE:|OUTPUT:" || true

# Extract and check
SEMI_OUT=$(echo "$OUTPUT" | grep "OUTPUT:" | sed 's/.*OUTPUT: //')
EXIT_CODE=$(echo "$OUTPUT" | grep "EXIT_CODE:" | grep -oP 'EXIT_CODE: \K[0-9-]+')

echo ""
echo "Exit code: $EXIT_CODE"
echo "Output: $SEMI_OUT"

if [ -n "$EXPECT" ]; then
    if echo "$SEMI_OUT" | grep -qF "$EXPECT"; then
        echo "PASS: output contains '$EXPECT'"
    else
        echo "FAIL: output does not contain '$EXPECT'"
        exit 1
    fi
fi

# Cleanup
rm -f "$TEST_NAME.o" "$TEST_NAME.elf" "$TEST_NAME.bin" "$TEST_NAME.pkg.vhd" *.cf tb_semi_run
