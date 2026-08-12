# RISC-V Gen2 bounded Zca load-effect outcome contract

Executable companion:
`test/01_unit/compiler/50.mir/hwir_zca_load_effect_outcomes_spec.spl`.

## Metadata

- Evidence class: source-level normalized outcome and effect-metadata contract.
- Scope: C.LW and C.LWSP only; neither scenario performs a memory operation.
- Requirements: REQ-G2-011 and NFR-G2-012.

## Scenarios and evidence steps

1. **C.LW effects.** Construct the bounded C.LW outcome and require explicit
   read/write constants, `match_legal`, and register-write/memory-read gates.
2. **C.LWSP reserved boundary.** Construct the bounded C.LWSP outcome and
   require its reserved-`rd` guard and tag classifier to suppress effects.

## Evidence boundary

These scenarios inspect source-level typed-HWIR effect metadata. They do not
issue or observe memory transactions, execute generated VHDL/RTL, prove all
load semantics, or qualify a processor or memory subsystem. Separate
self-hosted target, generated-RTL, and coverage receipts remain required for
qualification.
