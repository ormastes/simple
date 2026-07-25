#!/usr/bin/env bash
# RISC-V ISA gate runner — hand-written tests, run through GHDL, report pass/fail

# Don't exit on first error - we want to run all tests
# set -e

GATE_DIR="/home/ormastes/dev/pub/simple/test/riscv_isa_gate"
PAYLOADS_DIR="$GATE_DIR/payloads"
GHDL_WORK_DIR="/home/ormastes/dev/pub/simple/build/vhdl/rv32"

# Hand-written test set covering proven-bug areas
TESTS=(
  "simple"     # basic setup
  "add"        # arithmetic
  "addi"       # immediate arithmetic
  "mul"        # multiply (M extension)
  "div"        # divide (M extension)
  "rem"        # remainder (M extension)
  "jal"        # jump
  "beq"        # branch equal
  "lb"         # load byte
  "sw"         # store word
)

echo "RISC-V ISA Gate — rv32 GHDL Core"
echo "======================================"

mkdir -p "$PAYLOADS_DIR"

# Use tb_gate testbench - samples UART bytes for pass/fail
cd "$GHDL_WORK_DIR"
TESTBENCH="tb_gate"

# Compile testbench if not already done
if ! ghdl -r --std=08 $TESTBENCH --help > /dev/null 2>&1; then
  echo "Compiling testbench $TESTBENCH..."
  rm -f work-obj08.cf
  ghdl -a --std=08 rv32_exec_core.vhd tb_gate.vhd 2>&1 | head -5
  if ! ghdl -e --std=08 tb_gate 2>&1; then
    echo "ERROR: Failed to elaborate testbench $TESTBENCH"
    exit 1
  fi
fi

echo "Using testbench: $TESTBENCH"
echo ""

pass_count=0
fail_count=0
error_count=0

for test_name in "${TESTS[@]}"; do
  echo -n "Compiling $test_name... "

  # Use hand-written test
  src_file="$PAYLOADS_DIR/${test_name}.S"
  if [ ! -f "$src_file" ]; then
    echo "SOURCE NOT FOUND"
    ((error_count++))
    continue
  fi

  # Compile directly with gcc following build_minimal.sh recipe
  elf_file="$PAYLOADS_DIR/${test_name}.elf"
  riscv64-unknown-elf-gcc -march=rv32imac_zicsr -mabi=ilp32 -static -nostdlib \
    -Ttext=0x80000000 -o "$elf_file" "$src_file" 2>/dev/null || {
    echo "COMPILE FAIL"
    ((error_count++))
    continue
  }

  echo -n "Running... "

  # Convert ELF to .mem format following build_minimal.sh recipe
  bin_tmp="/tmp/${test_name}.bin"
  mem_file="$GHDL_WORK_DIR/rv32_payload.mem"

  riscv64-unknown-elf-objcopy -O binary "$elf_file" "$bin_tmp" 2>/dev/null || {
    echo "OBJCOPY FAIL"
    ((error_count++))
    continue
  }

  hexdump -v -e '1/4 "%08x\n"' "$bin_tmp" > "$mem_file"

  # Run GHDL simulation with timeout (longer timeout for complex tests)
  cd "$GHDL_WORK_DIR"
  timeout 15s ghdl -r --std=08 $TESTBENCH --stop-time=20ms > /tmp/gate_out.txt 2>&1 || true

  # Parse GATE_RESULT=PASS/FAIL line (check even if timeout occurred)
  result=$(grep "GATE_RESULT=" /tmp/gate_out.txt | head -1 | sed 's/GATE_RESULT=//')

  if [ -z "$result" ]; then
    echo "NO RESULT (timeout or UART issue)"
    ((error_count++))
  elif [ "$result" = "PASS" ]; then
    echo "PASS"
    ((pass_count++))
  elif [ "$result" = "FAIL" ]; then
    echo "FAIL"
    ((fail_count++))
  else
    echo "UNKNOWN (result=$result)"
    ((error_count++))
  fi
done

echo ""
echo "Summary:"
echo "  PASS:   $pass_count"
echo "  FAIL:   $fail_count"
echo "  ERROR:  $error_count"
