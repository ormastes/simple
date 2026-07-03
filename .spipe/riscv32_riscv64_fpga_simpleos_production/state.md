# Feature: riscv32_riscv64_fpga_simpleos_production

## Raw Request
make simple riscv 64 and 32 production level, let run simple os on both of then with fpga

## Task Type
feature

## Refined Goal
Make RV32 and RV64 SimpleOS FPGA support production-ready with repeatable local, RTL, QEMU, and physical-board evidence.

## Acceptance Criteria
- AC-1: RV32 and RV64 RTL smoke gates report both lanes in one run.
- AC-2: RV32 and RV64 SimpleOS build/run evidence exists and is current.
- AC-3: FPGA preflight reports tool, board, artifact, JTAG, UART, and bitstream status.
- AC-4: Physical FPGA boot is not marked done until a board bitstream, load path, UART marker, and SimpleOS payload all pass.
- AC-5: Current blockers are recorded in `doc/09_report/`.

## Scope Exclusions
Do not invent a second RISC-V core, bootloader, or FPGA framework. Reuse the existing RV32/RV64 RTL, SimpleOS QEMU, and Kria/K26 preflight scripts.

## Cooperative Review
N/A for this slice: this turn only fixes existing smoke wrappers and records blockers. Broad production completion still needs sidecar lanes for RV32, RV64, FPGA hardware, and SimpleOS boot.

## Evidence 2026-07-03
- `SIMPLE_BINARY=bin/release/simple sh scripts/check/check-riscv64-fpga-simpleos-preflight.shs --local-only`:
  - PASS: FT4232H USB present, serial ports present, openFPGALoader, OpenOCD, Vivado, RISC-V cross compilers, Simple hello.
  - FAIL: JTAG interface free, yosys, SimpleOS ELF artifact, SimpleOS bin artifact, SimpleOS bitstream artifact.
- `sh scripts/check/check-riscv-rtl-linux-smoke.shs --timeout=10`:
  - FAIL `generated_rv32_linux check-tools`: missing `examples/09_embedded/fpga_riscv/rtl` and `examples/09_embedded/fpga_riscv/sw/generated_rv32_smoke.s`.
  - FAIL `generated_rv64_linux check-tools`: missing `examples/09_embedded/fpga_riscv/rtl` and `examples/09_embedded/fpga_riscv/sw/generated_rv64_linux_handoff_smoke.s`.
- `SIMPLE_BINARY=bin/release/simple sh scripts/check/check-riscv-fpga-simpleos-preflight.shs --local-only`:
  - Reuses the RV64 preflight and additionally reports RV32 ELF, bin, and bitstream artifact status.
  - FAIL: RV32 ELF, bin, and bitstream artifacts are absent in this workspace.

## Phase
dev-in-progress

## Log
- dev: Created production-readiness lane and fixed existing smoke wrappers to expose both RV32/RV64 missing smoke artifacts.
- dev: Added dual-arch FPGA preflight wrapper so RV32 artifacts are checked beside the existing RV64 preflight.
