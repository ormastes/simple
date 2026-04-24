# System Test Plan: RV64 Linux RTL Pipeline

Date: 2026-04-24

Coverage goals:

- REQ-RV64-LINUX-RTL-001..005
  - canonical RV64 platform and truthful readiness tests
- REQ-RV64-LINUX-RTL-006..009
  - shared compiler/backend target contract tests
- REQ-RV64-LINUX-RTL-010
  - system traceability spec covering both hardware and compiler surfaces

Primary test entrypoints:

- `test/unit/hardware/riscv_common/riscv_linux_profile_spec.spl`
- `test/unit/hardware/fpga_linux/riscv_fpga_linux_spec.spl`
- `test/unit/compiler/backend/riscv_target_spec.spl`
- `test/feature/usage/llvm_backend_riscv64_spec.spl`
- `doc/06_spec/app/hardware/feature/rv64_linux_rtl_pipeline_spec.spl`
