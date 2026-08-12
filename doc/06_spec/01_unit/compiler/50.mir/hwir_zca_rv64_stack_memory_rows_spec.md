# RISC-V Gen2 bounded RV64 C.LDSP and C.SDSP typed-row contract

Executable companion:
`test/01_unit/compiler/50.mir/hwir_zca_rv64_stack_memory_rows_spec.spl`.

## Metadata

- Evidence class: source-level typed-HWIR stack-row and normalized-outcome
  contract.
- Profile: `rv64_zca_mission_critical`; RV32 is a rejection case only.
- Requirements: REQ-G2-001, REQ-G2-002, REQ-G2-011, NFR-G2-002,
  NFR-G2-003, and NFR-G2-012.

## Scenarios and evidence steps

1. **C.LDSP conversion contract.** Elaborate the row and require a valid typed
   graph, immediate reconstruction, reserved-`rd` guard, canonical selection,
   and the pinned vector constants.
2. **C.SDSP conversion contract.** Elaborate the row and require the stack
   immediate paths, canonical selection, and pinned vector constants.
3. **RV32 boundary.** Attempt both RV64-only stack rows under the RV32 critical
   configuration and require their dedicated rejection diagnostic.
4. **Explicit outcomes.** Construct both normalized outcomes and require every
   architectural-effect signal to be gated through `match_legal`.

## Evidence boundary

These scenarios are source-level typed-HWIR structure and effect-metadata
checks. They do not run generated VHDL/RTL, prove stack-memory transactions or
complete compressed-ISA behavior, or qualify a processor. Separate self-hosted
target, generated-RTL, and coverage gates remain required for qualification.
