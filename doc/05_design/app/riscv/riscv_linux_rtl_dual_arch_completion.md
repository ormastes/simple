# RISC-V Linux RTL Dual-Arch Completion Detail Design

- RV32 and RV64 each expose a `qemu_virt_*` machine helper and default empty Linux boot artifact bundle.
- `Rv32Machine.configure_linux_handoff()` writes `a0`, `a1`, and clears `satp`, matching the same public contract used by RV64.
- `RiscvFpgaLane` no longer encodes architecture truth itself; it references shared `RiscvLinuxProfile` and `RiscvPlatformProfile` data for each lane.
- Default manifest generation now emits both RV32 and RV64 bundles so readiness reporting stays dual-arch by default and neither lane is described as subordinate to the other.
- Each manifest lane carries product-level configuration metadata: ABI, MMU mode, configurable board/QEMU profile, RTL LUT budget, MHz target, and RVFI/SymbiYosys formal gate labels.
- Formal verification is split by layer: RVFI/SymbiYosys covers generated RTL
  execution-interface proof readiness, while Lean is reserved for Simple-level
  contracts such as product metadata consistency, scheduler/resource fairness,
  starvation freedom, race-condition constraints, and resource lifecycle
  invariants. A lane that touches both layers must collect both kinds of
  evidence before claiming full formal verification.
- Compiler/backend tests continue to validate that LLVM/native codegen reads target/triple/ABI defaults from the shared contract layer.
