# RISC-V Gen2 bounded RV64 C.LD and C.SD typed-row contract

Executable companion:
`test/01_unit/compiler/50.mir/hwir_zca_rv64_ld_sd_rows_spec.spl`.

## Metadata

- Evidence class: source-level typed-HWIR row and normalized-outcome contract.
- Profile: `rv64_zca_mission_critical`; RV32 is a rejection case only.
- Requirements: REQ-G2-001, REQ-G2-002, REQ-G2-011, NFR-G2-002,
  NFR-G2-003, and NFR-G2-012.

## Scenarios and evidence steps

1. **C.LD conversion contract.** Elaborate the row, require a structurally
   valid typed graph, pinned classifier/tag constants, immediate-shift paths,
   canonical selection, and the bounded reference vectors.
2. **C.SD conversion contract.** Elaborate the row and require its pinned
   store constants, immediate paths, canonical selection, and reference
   vectors.
3. **RV32 boundary.** Attempt both rows with the RV32 critical configuration
   and require their RV64-memory diagnostic.
4. **Explicit outcomes.** Construct the load and store outcomes and require
   `match_legal` to drive only the truthful register and memory effects.

## Evidence boundary

These are source-level typed-HWIR construction and effect-metadata checks. They
do not simulate emitted VHDL/RTL, demonstrate a memory transaction, prove all
compressed encodings, or qualify a processor or memory subsystem. Separate
self-hosted target, generated-RTL, and coverage gates remain required for any
qualification claim.
