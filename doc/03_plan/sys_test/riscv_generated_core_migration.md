# RISC-V Generated Core Migration System Test Plan

Date: 2026-04-29

## Acceptance Categories

- Truthfulness: manifests and scripts must identify external reference lanes distinctly from generated-core lanes.
- RV32 generated-core boundary: metadata must preserve semihost and mailbox as shell-owned services for the first runnable proof stage.
- RV64 generated-core boundary: metadata must preserve `FW_JUMP`/`a0`/`a1` Linux handoff expectations.

## Tests

1. `test/unit/hardware/riscv_common/riscv_generated_core_spec.spl`
   Verifies proof-lane labels and shell-contract defaults.
2. `test/unit/hardware/fpga_linux/riscv_fpga_linux_spec.spl`
   Verifies generated bundle metadata, readiness summaries, and scope labels.
3. `bash -n scripts/check-riscv-rtl-linux-smoke.shs scripts/rtl_riscv32_linux_litex.shs scripts/rtl_riscv64_linux_cva6.shs`
   Verifies script syntax after truth-label changes.
