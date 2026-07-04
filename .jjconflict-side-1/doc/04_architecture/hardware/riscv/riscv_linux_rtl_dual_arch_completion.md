# RISC-V Linux RTL Dual-Arch Completion Architecture

- `hardware.riscv_common.pkg.riscv_linux_pkg` is the sole public contract layer for ABI, XLEN, MMU mode, firmware mode, Linux handoff, and QEMU `virt` platform identity.
- `hardware.rv64gc` remains the repo-native RV64 Linux-capable CPU/SoC tree.
- `hardware.rv32gc` is the new repo-native RV32 Linux-capable CPU/SoC tree parallel in intent to RV64.
- `compiler.backend.riscv_target` remains the shared compiler/backend consumer of those public contracts.
- `hardware.fpga_linux.riscv_fpga_linux` is orchestration only: deterministic lane manifests, readiness reporting, and generated RTL bundle packaging.
- Readiness progression is explicit per architecture: `contract` -> `rtl-generated` -> `qemu-boot-validated` -> `rtl-linux-validated` -> `fpga-validated`.
