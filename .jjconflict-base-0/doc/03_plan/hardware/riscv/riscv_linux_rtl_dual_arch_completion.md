# RISC-V Linux RTL Dual-Arch Completion Agent Tasks

> Status: COMPLETE — spipe 16/16 done

- Task 1: promote shared RISC-V Linux/platform contracts to dual-arch public truth.
- Task 2: add a repo-native `rv32gc` hardware tree with a Linux-capable QEMU `virt` contract.
- Task 3: align FPGA orchestration/readiness logic to the shared contracts and dual-arch status reporting.
- Task 4: align compiler/backend tests and hardware contract tests with the shared truth.
- Task 5: run staged verification with generated-only RV32/RV64 Linux acceptance, leaving external RTL Linux runs as optional diagnostics.

## 2026-07-03 Product Metadata Hardening

- Added `scripts/check/check-riscv-fpga-sidecar-contract.shs` as the focused
  gate for generated generic and MLK-S02-100T bundles.
- The gate proves manifest board identity plus per-lane product level,
  configurable profile, RTL LUT/MHz budget, and RVFI/SymbiYosys formal metadata
  in the emitted RV32/RV64 debug sidecars.
- The current generated RV32 and RV64 cores have `observedRvfiPortCount = 17`
  and report sidecar formal status `rvfi-ready`; proof execution is still not
  claimed.
- Each generated lane now emits a formal harness (`*_formal.vhd`), SymbiYosys
  runner (`*.sby`), and formal manifest (`*_formal.sdn`) beside the generated
  core.
- The gate invokes `scripts/rtl/check-rvfi-formal-readiness.shs` with
  `CORE_VHDL=<generated core>` for both generated lanes so readiness remains
  tied to the shared RVFI structural-readiness script.
- Formal verification is two-track, not interchangeable:
  - RVFI/riscv-formal/SymbiYosys proves the generated RTL execution interface.
  - Lean should cover shared Simple-level contracts such as product metadata
    consistency, scheduler/resource fairness, starvation freedom, and
    race-condition/resource-lifecycle invariants when those become part of the
    lane. No Lean proof pass is claimed for this RISC-V lane yet.
- The RISC-V product Lean project separates generated definitions from added
  proofs: `Generated.lean` is the regeneration target, `Constraints.lean` is
  the manual proof layer, and `GENERATED_CONTRACT.md` records stable names.
