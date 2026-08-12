# RISC-V Gen2 bounded migrating Zca overlap-guard contract

Executable companion:
`test/01_unit/compiler/50.mir/hwir_migrating_overlap_guard_spec.spl`.

## Metadata

- Evidence class: source-level typed-HWIR ownership and emitter-text contract.
- Profile: bounded migrating Zca composition under the RV32 critical profile.
- Requirements: REQ-G2-011 and NFR-G2-012.

## Scenarios and evidence steps

1. **Unique-driver overlap guard.** Build the bounded migrating composition,
   require one owner for each public result, and require the no-overlap gate to
   suppress canonical output unless precisely one row is legal.
2. **Emitter representation.** Render the typed graph and require the emitted
   text to retain the no-overlap assignment and its canonical-instruction gate.

## Evidence boundary

This companion checks source-level typed ownership plus bounded generated text.
It does not simulate generated VHDL/RTL, exhaustively validate decoder
overlaps, or qualify a processor, complete ISA decoder, or retirement path.
Separate self-hosted target, generated-RTL, and coverage receipts remain
required for qualification.
