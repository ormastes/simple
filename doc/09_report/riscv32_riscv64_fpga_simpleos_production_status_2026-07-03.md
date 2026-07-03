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
- PASS: `build/os/simpleos_riscv64_fpga.elf` exists after `simple os build --scenario=riscv64-fpga-mmode`.
- PASS: `build/rv64_bringup_check/hello_litex_rv64.bin` is auto-derived from the RV64 ELF.
- PASS: `bin/release/simple` runs `hello_native.spl`.
- FAIL: JTAG interface is still bound to `ftdi_sio`.
- FAIL: `yosys` is not installed.
- FAIL: `build/build/xilinx_kv260/gateware/xilinx_kv260.bit` missing.

`SIMPLE_OS_BUILD_BACKEND=cranelift bin/release/simple os build --arch=riscv64 --scenario=riscv64-fpga-mmode`

- PASS: builds `build/os/simpleos_riscv64_fpga.elf`.
- PASS: auto-runs `llvm-objcopy -O binary` through the scenario build path and writes `build/rv64_bringup_check/hello_litex_rv64.bin`.

`SIMPLE_OS_BUILD_BACKEND=cranelift bin/release/simple os build --arch=riscv32 --scenario=riscv32-fpga-mmode`

- PASS: the scenario is registered and resolves to `build/os/simpleos_riscv32_fpga.elf`.
- FAIL: local release Simple cannot codegen RV32 with Cranelift (`Cranelift native builds do not support hosted riscv32 yet; use --backend llvm for this lane`), and this workspace does not have an LLVM-enabled Simple binary.

`sh scripts/check/check-riscv-rtl-linux-smoke.shs --timeout=10`

- PASS: generated RV32 Linux handoff smoke reports `GENERATED_RV32_LINUX_HANDOFF: PASS`.
- PASS: generated RV64 Linux handoff smoke reports `GENERATED_RV64_LINUX_HANDOFF: PASS`.

`bin/release/simple run src/hardware/fpga_linux/generate_riscv_fpga_bundle.spl /tmp/simple_riscv_bundle_check`

- PASS: emits generated-core RV32 and RV64 bundle files under `rv32/rtl` and `rv64/rtl`, including source, VHDL package/core, debug sidecar, and Linux handoff testbench artifacts.

`SIMPLE_BINARY=bin/release/simple sh scripts/check/check-riscv-fpga-simpleos-preflight.shs --local-only`

- Reuses the existing RV64 FPGA SimpleOS preflight.
- FAIL: `build/os/simpleos_riscv32_fpga.elf` missing.
- FAIL: `build/rv32_bringup_check/hello_litex_rv32.bin` missing.
- FAIL: `build/build/rv32_fpga/gateware/rv32_fpga.bit` missing.

## Change Landed In This Slice

The RTL smoke wrappers now resolve the repository root correctly and the top
level smoke script reports both RV32 and RV64 lane failures in one run instead
of stopping after the first missing artifact.

The generated Linux GHDL runners now use per-run generated bundle roots
(`$GEN_DIR/rv32/rtl` and `$GEN_DIR/rv64/rtl`) instead of directly compiling the
handwritten example RTL tree. The bundle generator has a small executable
entrypoint and no longer depends on the deleted handwritten RTL tree for its
bundle output.

Minimal RV32 and RV64 smoke assembly payloads are present under
`examples/09_embedded/fpga_riscv/sw/`, and the RV64 public smoke wrapper no
longer requires an unrelated native-build-capable compiler before running the
GHDL lane.

`scripts/check/check-riscv-fpga-simpleos-preflight.shs` now checks the existing
RV64 preflight plus RV32 FPGA artifacts, so production status cannot ignore the
32-bit lane.

`simple os build --scenario=riscv64-fpga-mmode` and
`simple os build --scenario=riscv32-fpga-mmode` are now registered. The RV64
FPGA lane builds with the local Cranelift-capable release compiler and emits
both ELF and raw bin payload artifacts. The RV32 lane is wired to the correct
FPGA entry/linker/output but remains blocked on an LLVM-enabled Simple compiler
for RV32 codegen in this workspace.

## Remaining Production Blockers

1. Install or provide `yosys` if synthesis/formal checks are part of the local
   production gate.
2. Free the FT4232H JTAG interface before physical FPGA programming.
3. Produce the current RV64 FPGA bitstream artifact.
4. Provide an LLVM-enabled Simple compiler and produce RV32 SimpleOS FPGA ELF/bin/bitstream artifacts.
5. Prove physical UART boot markers and SimpleOS payload execution on the board.

## Next Small Step

Install/provide an LLVM-enabled Simple compiler for RV32 and generate both
bitstreams, then rerun `scripts/check/check-riscv-fpga-simpleos-preflight.shs --local-only`.
