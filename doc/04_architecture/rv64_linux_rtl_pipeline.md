<!-- codex-design -->
# RISC-V Linux RTL Pipeline Architecture

Date: 2026-04-24

## Summary

This feature makes both RV32 and RV64 truthful Linux-capable hardware lanes and keeps LLVM as the truthful Linux-capable compiler lane. QEMU `virt` is the first proof contract. FPGA orchestration consumes that contract instead of inventing a second platform truth, and the repo-native `generated_rv32_linux` and `generated_rv64_linux` GHDL lanes are the primary in-repo Linux smoke paths.

## Capsules

- `hardware.riscv_common`
  - owns shared Linux profile, target ABI, firmware mode, MMU mode, and platform-profile contracts
- `hardware.rv32gc`
  - owns the RV32 QEMU `virt` Linux platform contract and the RV32 hardware behavior that implements it
- `hardware.rv64gc`
  - owns the RV64 QEMU `virt` Linux platform contract and the RV64 hardware behavior that implements it
- `hardware.fpga_linux`
  - owns board/build/readiness orchestration only
- `compiler.backend.riscv`
  - owns the compiler-facing RISC-V target contract: triple, ABI, features, `-march`, linker/sysroot defaults
- `compiler.backend.llvm`
  - consumes the shared RISC-V target contract for hosted and bare-metal RV64/RV32 setup
- `compiler.backend.native`
  - consumes the same shared target contract for stack alignment and Linux ABI consistency

## Boundaries

- Architectural truth about Linux boot compatibility lives in `hardware.riscv_common`, `hardware.rv32gc`, and `hardware.rv64gc`.
- Compiler target truth lives in `compiler.backend.riscv_target`.
- `hardware.fpga_linux` is not allowed to infer Linux readiness from generated stubs alone.
- `generated_rv32_linux` and `generated_rv64_linux` are separate authoritative proof lanes; external success does not prove either generated lane.
- Authoritative emitted RTL provenance is lane-local and must stay tagged as `simple-compiler-generated` in manifests and debug sidecars.

## Migration Notes

- `doc/04_architecture/rv64gc_cpu.md`, `riscv_fpga_linux.md`, and `rv32_multi_backend_boot.md` remain useful historical inputs.
- This document is the canonical architecture entry for the combined dual-arch RISC-V Linux RTL pipeline.
- FW_JUMP, DTB, real-DTB, and MMU proof gates remain bounded proof gates that must pass before the long-running generated Linux smoke.
- `rtl-linux-validated` for both RV32 and RV64 means the generated GHDL lane observed Linux UART markers, not only handoff-state proofs.
