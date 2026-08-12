# RISC-V Gen2 target-trap product closure direct-API contract

Executable companion:
`test/01_unit/compiler/50.mir/hwir_zca_product_frontend_spec.spl`.

## Metadata

- Evidence class: direct compiler API typed-HWIR elaboration and deterministic
  VHDL-text contract.
- Products: RV32 C.JAL critical and RV64 C.ADDIW critical.
- Requirements: REQ-G2-002, REQ-G2-010, REQ-G2-011, NFR-G2-010,
  NFR-G2-011, and NFR-G2-012.

## Scenarios and evidence steps

1. **Product ISA closure.** Query the direct typed-HWIR API for each concrete
   target profile and require 26
   RV32 rows and 32 RV64 rows. The RV64-only load/store and word-operation rows
   must be present only in the RV64 product.
2. **Row ambiguity guard.** Build the complete RV64 typed-HWIR decoder, require a valid
   graph and exactly one row-level overlap guard, and retain origins for every
   RV64-only row.
3. **Deterministic specialized artifact.** Call the direct compiler API for the
   RV64 stateful product twice, require identical 64-character HWIR digests,
   and inspect the emitted
   typed decoder names for the selected rows and overlap guard.
4. **Fail-closed configuration boundary.** Attempt the full RV64 graph under
   an RV32 product configuration and require the dedicated
   `HWIR-E-ZCA-RV64-FULL-PROFILE` diagnostic.

## Evidence boundary

These scenarios establish direct-API source-level typed composition, profile
selection, and deterministic VHDL serialization. They do not run generated
VHDL in GHDL, prove complete RTL behavior or target equivalence, or qualify an
architectural retirement producer.
Mission-critical release evidence still requires self-hosted RV32/RV64 target
receipts, coverage measurement, and the separate generated-RTL qualification
gates.
