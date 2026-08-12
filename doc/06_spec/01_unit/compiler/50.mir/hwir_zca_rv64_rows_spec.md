# RISC-V Gen2 bounded RV64 Zca OP-32 and shift-row contract

Executable companion:
`test/01_unit/compiler/50.mir/hwir_zca_rv64_rows_spec.spl`.

## Metadata

- Evidence class: source-level typed-HWIR row and normalized-outcome contract.
- Scope: RV64 C.ADDW/C.SUBW and C.SLLI/C.SRLI/C.SRAI six-bit shift rows.
- Requirements: REQ-G2-001, REQ-G2-002, REQ-G2-011, NFR-G2-002,
  NFR-G2-003, and NFR-G2-012.

## Scenarios and evidence steps

1. **OP-32 classifiers.** Elaborate C.ADDW and C.SUBW under the concrete RV64
   profile and require each typed row to expose its classifier and selection
   structure.
2. **RV32 boundary.** Attempt the RV64-only OP-32 rows with the RV32 profile
   and require the typed RV64 rejection diagnostic.
3. **Six-bit shifts.** Elaborate C.SLLI, C.SRLI, and C.SRAI, require their
   `shamt_high` signal and classifier structures, and reject every row in RV32.
4. **Explicit outcomes.** Construct each normalized outcome and require the
   explicit legality and register/memory effect signals without a canonical
   sentinel oracle.

## Evidence boundary

These are source-level typed-HWIR construction and metadata checks. They do
not execute generated VHDL/RTL, prove all compressed-ISA semantics, or qualify
an RV64 processor or retirement path. Separate self-hosted target,
generated-RTL, and coverage receipts remain required for qualification.
