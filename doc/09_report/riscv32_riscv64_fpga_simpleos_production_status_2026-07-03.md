# RISC-V32/RISC-V64 FPGA SimpleOS Production Status - 2026-07-03

## Status

STATUS: NOT PRODUCTION READY.

The repo has RV32/RV64 RTL, SimpleOS QEMU, Kria/K26 FPGA preflight scripts, and
existing reports. Current local evidence does not prove production FPGA boot for
either RV32 or RV64.

## Fresh Evidence

`SIMPLE_BINARY=bin/release/simple sh scripts/check/check-riscv64-fpga-simpleos-preflight.shs --local-only`

- PASS: FT4232H USB present.
- PASS: `/dev/ttyUSB0` through `/dev/ttyUSB3` present.
- PASS: openFPGALoader, OpenOCD, Vivado, `riscv64-unknown-elf-gcc`, and `riscv64-linux-gnu-gcc`.
- PASS: `bin/release/simple` runs `hello_native.spl`.
- FAIL: JTAG interface is still bound to `ftdi_sio`.
- FAIL: `yosys` is not installed.
- FAIL: `build/os/simpleos_riscv64_fpga.elf` missing.
- FAIL: `build/rv64_bringup_check/hello_litex_rv64.bin` missing.
- FAIL: `build/build/xilinx_kv260/gateware/xilinx_kv260.bit` missing.

`sh scripts/check/check-riscv-rtl-linux-smoke.shs --timeout=10`

- FAIL: missing `examples/09_embedded/fpga_riscv/rtl`.
- FAIL: missing `examples/09_embedded/fpga_riscv/sw/generated_rv32_smoke.s`.
- FAIL: missing `examples/09_embedded/fpga_riscv/sw/generated_rv64_linux_handoff_smoke.s`.

`SIMPLE_BINARY=bin/release/simple sh scripts/check/check-riscv-fpga-simpleos-preflight.shs --local-only`

- Reuses the existing RV64 FPGA SimpleOS preflight.
- FAIL: `build/os/simpleos_riscv32_fpga.elf` missing.
- FAIL: `build/rv32_bringup_check/hello_litex_rv32.bin` missing.
- FAIL: `build/build/rv32_fpga/gateware/rv32_fpga.bit` missing.

## Change Landed In This Slice

The RTL smoke wrappers now resolve the repository root correctly and the top
level smoke script reports both RV32 and RV64 lane failures in one run instead
of stopping after the first missing artifact.

`scripts/check/check-riscv-fpga-simpleos-preflight.shs` now checks the existing
RV64 preflight plus RV32 FPGA artifacts, so production status cannot ignore the
32-bit lane.

## Remaining Production Blockers

1. Restore or generate the RV32 and RV64 smoke assembly payloads used by the
   generated RTL Linux smoke runners.
2. Restore or regenerate the `examples/09_embedded/fpga_riscv/rtl` VHDL testbench tree.
3. Install or provide `yosys` if synthesis/formal checks are part of the local
   production gate.
4. Free the FT4232H JTAG interface before physical FPGA programming.
5. Produce current RV64 FPGA SimpleOS ELF/bin/bitstream artifacts.
6. Add equivalent RV32 SimpleOS FPGA artifact evidence, not only RV64.
7. Prove physical UART boot markers and SimpleOS payload execution on the board.

## Next Small Step

Restore the two missing smoke payloads or change the wrappers to point at their
current generated location, then rerun `scripts/check/check-riscv-rtl-linux-smoke.shs`.
