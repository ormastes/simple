# RV64 Linux RTL Pipeline — Domain Research

Date: 2026-04-24

External constraints carried into this feature from the selected implementation plan:

- RISC-V psABI default Linux ABIs:
  - RV64G uses `LP64D`
  - RV32G uses `ILP32D`
- Linux RISC-V boot contract requires:
  - `a0 = hartid`
  - `a1 = dtb`
  - MMU disabled on entry (`satp = 0`)
  - kernel load alignment suitable for the platform handoff
- QEMU `virt` is the canonical first validation platform because it standardizes:
  - CLINT
  - PLIC
  - UART
  - generated DTB
  - OpenSBI-oriented Linux handoff
- Sv39 invalidation and ordering must remain consistent with `SFENCE.VMA` expectations.

These constraints are used as design inputs for the shared Linux/platform profile types and for the RV64 contract tests in this feature.
