#!/bin/bash
# Run a RISC-V assembly test on the simulated RV32I CPU
# Usage: ./run_test.sh test_add.s [expected_led_value]
#
# Pipeline: .s → assemble → ELF → binary → VHDL mem init → GHDL simulate → check LED
#
# TODO: create gen_pkg_vhd.shs to regenerate .pkg.vhd files from .c/.s sources
#       without running the full simulation (steps 1-3 only).
#       The .pkg.vhd files are gitignored because test_c_runtime.pkg.vhd is ~3GB.

set -e
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
RTL_DIR="$SCRIPT_DIR/../rtl"
TEST_SRC="$1"
EXPECT_LED="${2:--1}"
TEST_NAME="${TEST_SRC%.s}"
TEST_NAME="${TEST_NAME%.spl}"

if [ -z "$TEST_SRC" ]; then
    echo "Usage: $0 <test.s> [expected_led_value]"
    exit 1
fi

echo "=== RV32I Simulation Test: $TEST_SRC ==="

EXT="${TEST_SRC##*.}"

# Step 1: Compile/Assemble based on file type
if [ "$EXT" = "s" ]; then
    echo "[1/5] Assembling..."
    riscv64-linux-gnu-as -march=rv32im -mabi=ilp32 -o "$TEST_NAME.o" "$TEST_SRC"
    riscv64-linux-gnu-ld -m elf32lriscv -Ttext=0x0 -o "$TEST_NAME.elf" "$TEST_NAME.o"
elif [ "$EXT" = "c" ]; then
    echo "[1/5] Compiling C..."
    riscv64-linux-gnu-gcc -march=rv32i -mabi=ilp32 -nostdlib -nostartfiles \
        -Wl,-Ttext=0x0,--no-warn-rwx-segment,--section-start=.text.start=0x0 \
        -static -O2 -o "$TEST_NAME.elf" "$TEST_SRC"
elif [ "$EXT" = "elf" ]; then
    echo "[1/5] Using existing ELF..."
    cp "$TEST_SRC" "$TEST_NAME.elf"
else
    echo "Unsupported file type: $EXT"
    exit 1
fi

# Step 2: Extract binary (.text section only)
echo "[2/5] Extracting binary..."
riscv64-linux-gnu-objcopy -O binary -j .text "$TEST_NAME.elf" "$TEST_NAME.bin"

# Step 3: Generate VHDL memory init package
echo "[3/5] Generating VHDL memory package..."
python3 -c "
import struct, sys
data = open('$TEST_NAME.bin', 'rb').read()
# Pad to 4-byte alignment
while len(data) % 4 != 0:
    data += b'\x00'
words = []
for i in range(0, len(data), 4):
    w = struct.unpack('<I', data[i:i+4])[0]
    words.append(w)
print('-- Auto-generated from $TEST_SRC')
print('library ieee;')
print('use ieee.std_logic_1164.all;')
print('package test_program is')
print('    type word_array_t is array (natural range <>) of std_logic_vector(31 downto 0);')
print('    constant PROGRAM_SIZE : integer := %d;' % len(words))
print('    constant PROGRAM_DATA : word_array_t(0 to %d) := (' % (len(words)-1))
for i, w in enumerate(words):
    comma = ',' if i < len(words)-1 else ''
    print('        x\"%08x\"%s  -- %03x' % (w, comma, i*4))
print('    );')
print('end package test_program;')
" > "$TEST_NAME.pkg.vhd"

# Step 4: Generate test-specific top with IMEM loaded
cat > "$TEST_NAME.tb.vhd" << 'EOVHDL'
-- Auto-generated testbench for PROGRAM
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.test_program.all;

entity tb_test is
end entity tb_test;

architecture sim of tb_test is
    constant CLK_PERIOD : time := 10 ns;
    signal clk     : std_logic := '0';
    signal reset_n : std_logic := '0';
    signal imem_addr  : std_logic_vector(31 downto 0);
    signal imem_data  : std_logic_vector(31 downto 0);
    signal dmem_addr  : std_logic_vector(31 downto 0);
    signal dmem_wdata : std_logic_vector(31 downto 0);
    signal dmem_rdata : std_logic_vector(31 downto 0);
    signal dmem_we, dmem_re : std_logic;
    signal dmem_width : std_logic_vector(1 downto 0);
    signal halted : std_logic;

    type mem_t is array (0 to 1023) of std_logic_vector(31 downto 0);
    signal dmem : mem_t := (others => (others => '0'));
    signal led_reg : std_logic_vector(31 downto 0) := (others => '0');
    signal done : boolean := false;
begin
    u_cpu : entity work.rv32i_core
        generic map (RESET_ADDR => x"00000000")
        port map (clk=>clk, reset_n=>reset_n,
                  imem_addr=>imem_addr, imem_data=>imem_data,
                  dmem_addr=>dmem_addr, dmem_wdata=>dmem_wdata,
                  dmem_rdata=>dmem_rdata, dmem_we=>dmem_we,
                  dmem_re=>dmem_re, dmem_width=>dmem_width,
                  halted=>halted);

    clk <= not clk after CLK_PERIOD/2 when not done else '0';

    -- IMEM from package
    imem_data <= PROGRAM_DATA(to_integer(unsigned(imem_addr(11 downto 2))))
                 when to_integer(unsigned(imem_addr(11 downto 2))) < PROGRAM_SIZE
                 else x"00000013";

    -- DMEM + MMIO
    process(clk) begin
        if rising_edge(clk) then
            if dmem_we = '1' then
                if dmem_addr(31) = '1' and dmem_addr(3 downto 0) = x"0" then
                    led_reg <= dmem_wdata;
                elsif dmem_addr(31) = '0' then
                    dmem(to_integer(unsigned(dmem_addr(11 downto 2)))) <= dmem_wdata;
                end if;
            end if;
        end if;
    end process;

    dmem_rdata <= led_reg when (dmem_re='1' and dmem_addr(31)='1' and dmem_addr(3 downto 0)=x"0") else
                  dmem(to_integer(unsigned(dmem_addr(11 downto 2)))) when (dmem_re='1' and dmem_addr(31)='0') else
                  (others => '0');

    process
        variable cycles : integer := 0;
    begin
        reset_n <= '0';
        wait for CLK_PERIOD * 5;
        reset_n <= '1';
        while halted='0' and cycles < 100000 loop
            wait for CLK_PERIOD;
            cycles := cycles + 1;
        end loop;
        report "CYCLES: " & integer'image(cycles);
        report "LED: " & integer'image(to_integer(unsigned(led_reg)));
        done <= true;
        wait;
    end process;
end architecture sim;
EOVHDL

# Step 5: Compile and simulate (all in same work dir)
echo "[4/5] Compiling VHDL..."
ghdl -a --std=08 "$RTL_DIR/rv32i_pkg.vhd" "$RTL_DIR/regfile.vhd" "$RTL_DIR/alu.vhd" "$RTL_DIR/decoder.vhd" "$RTL_DIR/rv32i_core.vhd"
ghdl -a --std=08 "$TEST_NAME.pkg.vhd"
ghdl -a --std=08 "$TEST_NAME.tb.vhd"
ghdl -e --std=08 tb_test

echo "[5/5] Simulating..."
OUTPUT=$(ghdl -r --std=08 tb_test --stop-time=2ms 2>&1)
echo "$OUTPUT" | grep -E "CYCLES:|LED:|PASS|FAIL|error"

# Extract LED value and check
LED_VAL=$(echo "$OUTPUT" | grep "LED:" | grep -oP 'LED: \K[0-9]+')
echo ""
echo "Result: LED = $LED_VAL"

if [ "$EXPECT_LED" != "-1" ]; then
    if [ "$LED_VAL" = "$EXPECT_LED" ]; then
        echo "PASS: LED=$LED_VAL (expected $EXPECT_LED)"
        EXIT_CODE=0
    else
        echo "FAIL: LED=$LED_VAL (expected $EXPECT_LED)"
        EXIT_CODE=1
    fi
else
    echo "(no expected value specified)"
    EXIT_CODE=0
fi

# Cleanup
rm -f "$TEST_NAME.o" "$TEST_NAME.elf" "$TEST_NAME.bin" "$TEST_NAME.pkg.vhd" "$TEST_NAME.tb.vhd" *.o *.cf tb_test
exit $EXIT_CODE
