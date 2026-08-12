# RISC-V Gen2 bounded RV64 Zca row identity contract

Executable companion:
`test/01_unit/compiler/50.mir/hwir_zca_rv64_contract_spec.spl`.

## Metadata

- Evidence class: source-level reserved MIR identity and allowlist contract.
- Scope: the nine isolated RV64 Zca row identifiers only.
- Requirements: REQ-G2-001, REQ-G2-008, NFR-G2-002, and NFR-G2-009.

## Scenarios and evidence steps

1. **Closed identity list.** Read the intrinsic and ISA lists, require all
   nine entries, their pinned boundary entries, and identity equality between
   the ISA list and row-level evidence allowlist.
2. **Exact admission boundary.** Admit a reserved intrinsic identifier while
   rejecting a suffix lookalike and an unknown identifier.

## Evidence boundary

This is a source-level contract for names and bounded evidence scope. It does
not execute generated VHDL/RTL, prove the rows implement all ISA semantics, or
qualify an RV64 processor or Zca product. Qualification remains dependent on
the separate self-hosted target, generated-RTL, and coverage evidence gates.
