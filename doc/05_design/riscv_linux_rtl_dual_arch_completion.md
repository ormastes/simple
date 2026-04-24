# RISC-V Linux RTL Dual-Arch Completion Detail Design

- RV32 and RV64 each expose a `qemu_virt_*` machine helper and default empty Linux boot artifact bundle.
- `Rv32Machine.configure_linux_handoff()` writes `a0`, `a1`, and clears `satp`, matching the same public contract used by RV64.
- `RiscvFpgaLane` no longer encodes architecture truth itself; it references shared `RiscvLinuxProfile` and `RiscvPlatformProfile` data for each lane.
- Default manifest generation now emits both RV32 and RV64 bundles so readiness reporting stays dual-arch by default.
- Compiler/backend tests continue to validate that LLVM/native codegen reads target/triple/ABI defaults from the shared contract layer.
