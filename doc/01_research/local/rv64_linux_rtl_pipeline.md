# RV64 Linux RTL Pipeline — Local Research

Date: 2026-04-24

Inputs reviewed:

- `doc/04_architecture/rv64gc_cpu.md`
- `doc/04_architecture/riscv_fpga_linux.md`
- `doc/04_architecture/rv32_multi_backend_boot.md`
- `src/hardware/rv64gc/**`
- `src/hardware/fpga_linux/riscv_fpga_linux.spl`
- `src/compiler/70.backend/backend/llvm_target.spl`
- `src/compiler/70.backend/backend/llvm_cross_target.spl`
- `src/compiler/70.backend/backend/native/isel_riscv64.spl`
- `src/compiler/70.backend/backend/native/encode_riscv64.spl`

Findings:

- `src/hardware/rv64gc/**` already owns a real RV64GC CPU/SoC implementation with QEMU `virt`-aligned addresses.
- `src/hardware/fpga_linux/riscv_fpga_linux.spl` still encodes readiness as generated text contracts and mixes RV32/RV64 Linux claims in one prepare layer.
- LLVM target support already exists for `riscv64` and `riscv32`, but the Linux ABI/triple policy is not centralized in one shared RISC-V backend capsule.
- Native RV32/RV64 backends exist but currently duplicate ABI and calling-convention assumptions instead of consuming one shared target contract.
- Existing RV32 docs prove compiler/boot-contract coverage, but there is no matching `src/hardware/rv32*` CPU tree to justify first-class RV32 Linux CPU/RTL claims.

Selected scope:

- Canonical feature: `rv64_linux_rtl_pipeline`
- Primary hardware lane: RV64
- Primary compiler lane: LLVM
- First proof platform: QEMU `virt`
- `hardware.fpga_linux` becomes orchestration only
