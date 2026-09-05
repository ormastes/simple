# Precise Scalar Trap Retirement Projection

**Executable companion:** `test/01_unit/compiler/50.mir/hwir_riscv_scalar_trap_projection_spec.spl`

## Purpose and scope

This focused source-level unit specification builds the strict scalar
trap/interrupt projection into the retirement-owner dispatch ABI for concrete
RV32 and RV64 configurations. It checks typed port widths, the fixed event
priority, invalid-payload normalization, and suppression of architectural
write payloads while a valid trap or interrupt is dispatched.

For one valid input, the projection gives memory exception precedence over
execute exception, execute exception precedence over illegal instruction, and
all synchronous exceptions precedence over an interrupt. Illegal instructions
use cause 2 and preserve the original fetched encoding as `tval`.

## Scenarios

1. Build the same typed projection contract for RV32 and RV64 and inspect the
   concrete XLEN-dependent dispatch widths.
2. Inspect the HWIR select graph for memory/execute/illegal/interrupt priority
   and for cause and `tval` selection.
3. Inspect guarded dispatch selects that suppress register and memory writes
   and normalize inactive cause and `tval` fields.
4. Evaluate an invalid input with every event asserted and confirm that every
   trap, interrupt, cause, and architectural-write output is inactive or zero.
5. Evaluate simultaneous events to confirm memory, then execute, then illegal
   selection, with synchronous events suppressing the interrupt.
6. Reject an empty stable module identity with the documented diagnostic.

## Requirement traceability

- REQ-G2-001 — the projected ABI is a typed HWIR module with explicit typed
  ports, operations, origins, and normalized output contracts.
- REQ-G2-002 — RV32 and RV64 are selected as concrete elaboration-time
  configurations and give concrete XLEN-width ports.
- NFR-G2-002 — empty module identity fails with a stable diagnostic and an
  invalid input cannot leak a placeholder trap payload.
- NFR-G2-003 — the projection has selected concrete RV32/RV64 widths rather
  than an XLEN runtime selector.

## Evidence boundary

This is source-level combinational HWIR and host-evaluator evidence for a
single-event priority and normalization adapter. It does not own state, take a
real trap, update privilege/CSR state, perform a pipeline flush or interrupt
acknowledgement, connect to the retirement owner, emit or simulate VHDL, prove
precise architectural exceptions, or qualify hardware correctness.
