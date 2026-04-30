<!-- codex-design -->
# RV64 Linux RTL Pipeline Architecture

Date: 2026-04-24

## Summary

This feature makes RV64 the truthful Linux-capable hardware lane and makes LLVM the truthful Linux-capable compiler lane. QEMU `virt` is the first proof contract. FPGA orchestration consumes that contract instead of inventing a second platform truth, and the repo-native `generated_rv64_linux` GHDL lane is the primary in-repo Linux smoke path.

## Capsules

- `hardware.riscv_common`
  - owns shared Linux profile, target ABI, firmware mode, MMU mode, and platform-profile contracts
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

- Architectural truth about Linux boot compatibility lives in `hardware.riscv_common` and `hardware.rv64gc`.
- Compiler target truth lives in `compiler.backend.riscv_target`.
- `hardware.fpga_linux` is not allowed to infer Linux readiness from generated stubs alone.
- `generated_rv64_linux` and `reference_external_rv64_linux` are separate proof lanes; external success does not prove the generated lane.
- RV32 stays config/parity scope until a real `src/hardware/rv32*` CPU tree exists.

## Migration Notes

- `doc/04_architecture/rv64gc_cpu.md`, `riscv_fpga_linux.md`, and `rv32_multi_backend_boot.md` remain useful historical inputs.
- This document is the canonical architecture entry for the combined RV64 Linux RTL pipeline.
- FW_JUMP, DTB, real-DTB, and Sv39 remain bounded proof gates that must pass before the long-running generated Linux smoke.
- `rtl-linux-validated` for RV64 means the generated GHDL lane observed Linux UART markers, not only handoff-state proofs.
