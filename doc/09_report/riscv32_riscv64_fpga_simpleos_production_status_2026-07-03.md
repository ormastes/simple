# RISC-V32/RISC-V64 FPGA SimpleOS Production Status - 2026-07-03

## Status

STATUS: NOT PRODUCTION READY.

The repo has RV32/RV64 RTL, SimpleOS QEMU, Kria/K26 FPGA preflight scripts, and
existing reports. Current local evidence does not prove production FPGA boot for
either RV32 or RV64.

## Fresh Evidence

`SIMPLE_BINARY=bin/release/simple sh scripts/check/check-riscv64-fpga-simpleos-preflight.shs --local-only`

- PASS: FT4232H USB present.
- PASS: serial ports present.
- PASS: JTAG interface is free.
- PASS: openFPGALoader, OpenOCD, Vivado, `riscv64-unknown-elf-gcc`, and `riscv64-linux-gnu-gcc`.
- PASS: `build/os/simpleos_riscv64_fpga.elf` exists after `simple os build --scenario=riscv64-fpga-mmode`.
- PASS: `build/rv64_bringup_check/hello_litex_rv64.bin` is auto-derived from the RV64 ELF.
- PASS: `build/build/xilinx_kv260/gateware/xilinx_kv260.bit` exists after the K26 Vivado build.
- PASS: `bin/release/simple` runs `hello_native.spl`.
- FAIL: `yosys` is not installed.
- FAIL: `build/vhdl/rv64/rv64gc_core.vhd` is a placeholder core with no instruction execution or debug/load context.
- FAIL: `build/fpga/k26/load_elf_k26.log` records XSDB `dow` failure with `Invalid context`.

`SIMPLE_BINARY=bin/release/simple bash scripts/fpga/build_k26_vexriscv.shs`

- PASS: generates RV64 VHDL with `bin/release/simple`.
- PASS: Vivado synthesis and implementation complete.
- PASS: DRC reports 0 errors after constraining `uart_tx` to K26 PMOD H12/LVCMOS33.
- PASS: bitgen completes and writes `build/fpga/k26/k26_vexriscv.bit` plus `build/build/xilinx_kv260/gateware/xilinx_kv260.bit`.

`SIMPLE_BINARY=bin/release/simple CAPTURE_SECONDS=5 LINUX_TIMEOUT=10 sh scripts/fpga/check_kv260_simple_rv64_linux.shs`

- PASS: RV64 bitstream and ELF artifacts are present.
- PASS: RV64 ELF header is ELF64 RISC-V.
- PASS: KV260 bitstream loads through Vivado.
- PASS: merged USB PS UART responds.
- PASS: generated RV64 Linux handoff smoke passes.
- INFO: PL UART on merged USB has no output; current image still requires PMOD UART capture or a routed PL UART to prove SimpleOS payload execution.

`bash scripts/fpga/load_elf_k26.shs`

- PASS: programs the generated K26 bitstream through XSDB.
- FAIL: `dow build/os/simpleos_riscv64_fpga.elf` returns XSDB `Invalid context`; the generated bitstream does not expose a usable CPU/debug context for ELF download.

`SIMPLE_BINARY=bin/release/simple sh scripts/check/check-riscv-fpga-simpleos-preflight.shs --local-only`

- PASS: RV64 ELF, raw bin, and bitstream artifacts exist.
- PASS: RV32 ELF and raw bin artifacts exist after the LLVM-driver build.
- FAIL: `rv64_fpga_core_executable` because the generated active core is a placeholder.
- FAIL: `rv64_fpga_elf_load_context` because the last XSDB load log reports `xsdb-dow-invalid-context`.
- FAIL: `build/build/rv32_fpga/gateware/rv32_fpga.bit` is still missing.

`SIMPLE_OS_BUILD_BACKEND=cranelift bin/release/simple os build --arch=riscv64 --scenario=riscv64-fpga-mmode`

- PASS: builds `build/os/simpleos_riscv64_fpga.elf`.
- PASS: auto-runs `llvm-objcopy -O binary` through the scenario build path and writes `build/rv64_bringup_check/hello_litex_rv64.bin`.

`SIMPLE_OS_BUILD_BACKEND=cranelift bin/release/simple os build --arch=riscv32 --scenario=riscv32-fpga-mmode`

- PASS: the scenario is registered and resolves to `build/os/simpleos_riscv32_fpga.elf`.
- FAIL: local release Simple cannot codegen RV32 with Cranelift (`Cranelift native builds do not support hosted riscv32 yet; use --backend llvm for this lane`).

`env LLVM_SYS_180_PREFIX=/usr SIMPLE_LIB=src SIMPLE_BINARY=src/compiler_rust/target/debug/simple SIMPLE_OS_BUILD_BACKEND=llvm src/compiler_rust/target/debug/simple os build --scenario=riscv32-fpga-mmode`

- PASS: local LLVM-enabled Rust Simple driver builds `build/os/simpleos_riscv32_fpga.elf`.
- PASS: scenario objcopy writes `build/rv32_bringup_check/hello_litex_rv32.bin`.

`sh scripts/check/check-riscv-rtl-linux-smoke.shs --timeout=10`

- PASS: generated RV32 Linux handoff smoke reports `GENERATED_RV32_LINUX_HANDOFF: PASS`.
- PASS: generated RV64 Linux handoff smoke reports `GENERATED_RV64_LINUX_HANDOFF: PASS`.

`bin/release/simple run src/hardware/fpga_linux/generate_riscv_fpga_bundle.spl /tmp/simple_riscv_bundle_check`

- PASS: emits generated-core RV32 and RV64 bundle files under `rv32/rtl` and `rv64/rtl`, including source, VHDL package/core, debug sidecar, and Linux handoff testbench artifacts.

`SIMPLE_BINARY=bin/release/simple sh scripts/check/check-riscv-fpga-simpleos-preflight.shs --local-only`

- Reuses the existing RV64 FPGA SimpleOS preflight.
- PASS: `build/os/simpleos_riscv32_fpga.elf` exists.
- PASS: `build/rv32_bringup_check/hello_litex_rv32.bin` exists.
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
both ELF and raw bin payload artifacts. The RV32 lane builds with the local
LLVM-enabled Rust Simple driver and emits both ELF and raw bin payload
artifacts.

The K26 Vivado wrapper now uses the release Simple binary fallback, regenerates
the RV64 VHDL/TCL every run, emits a K26 UART XDC constraint, preserves Vivado
failure status despite tailing logs, and copies the generated bitstream to the
preflight path. The K26 ELF loader now defaults to the current RV64 FPGA ELF and
keeps an XSDB failure log at `build/fpga/k26/load_elf_k26.log`.

## Remaining Production Blockers

1. Install or provide `yosys` if synthesis/formal checks are part of the local
   production gate.
2. Replace the generated RV64 stub softcore bitstream with a real CPU/debug/load path; current XSDB `dow` fails with `Invalid context`.
3. Capture RV64 PL UART boot markers from PMOD H12/E10 or route PL UART to an observable serial channel.
4. Produce an RV32 FPGA bitstream and prove RV32 SimpleOS payload execution.

## Next Small Step

Prove RV64 SimpleOS payload execution on the programmed FPGA: either add a real
softcore debug/load path for `build/os/simpleos_riscv64_fpga.elf` or capture the
expected SimpleOS UART markers from the PMOD H12/E10 PL UART.
