# RISC-V Linux RTL Dual-Arch Completion System Test Plan

1. Verify shared Linux/platform contracts for `qemu_virt_rv32` and `qemu_virt_rv64`.
2. Verify repo-native RV32 and RV64 machine-level Linux handoff contracts.
3. Verify backend target contracts stay aligned with the shared platform profiles.
4. Verify FPGA orchestration emits deterministic dual-arch manifests and RTL bundles.
5. Run `sh scripts/check-riscv-rtl-linux-smoke.shs --check-tools`.
6. Run `sh scripts/check-riscv-rtl-linux-smoke.shs --rv32-only`.
7. Run `sh scripts/check-riscv-rtl-linux-smoke.shs --rv64-only`.
