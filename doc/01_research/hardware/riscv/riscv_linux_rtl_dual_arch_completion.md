# RISC-V Linux RTL Dual-Arch Completion — Local Research

- Existing repo-native hardware already contains a broad `src/hardware/rv64gc` tree with QEMU `virt`-style memory map contracts.
- Shared Linux/platform truth was already moving into `src/hardware/riscv_common/pkg/riscv_linux_pkg.spl`, but RV32 was still modeled as compiler parity only.
- `src/hardware/fpga_linux/riscv_fpga_linux.spl` had become the readiness/orchestration choke point and was still defaulting to RV64-only emission.
- Native and LLVM backends already consume shared RISC-V target contracts in `src/compiler/70.backend/backend/riscv_target.spl`.
- Missing implementation gap was a repo-native `src/hardware/rv32gc` tree plus dual-arch contract propagation into orchestration/tests/docs.
