# Typed Scalar Retirement Owner

**Executable companion:** `test/01_unit/compiler/50.mir/hwir_riscv_scalar_retirement_owner_spec.spl`

## Purpose and scope

This focused source-level unit specification builds the strict one-entry
architectural-retirement owner for concrete RV32 and RV64 products. It checks
the closed sequential-plan shape, typed record and lineage widths, conservative
one-entry dispatch admission, guarded retirement payloads, synchronous reset,
and the terminal-order protocol-fault condition in generated strict VHDL.

The owner is self-contained: it has no child entity, decoder pins, or hidden
dispatch `xlen` port. It assigns a monotonic 64-bit retirement order until the
terminal order is accepted, at which point it records a protocol fault and
stops further admission.

## Scenarios

1. Build normalized one-record owners for RV32 and RV64 and inspect their
   diagnostics, owner shape, typed widths, and ordered `consume`,
   `capture_terminal_order`, and `capture` rules.
2. Emit RV64 strict VHDL and inspect conservative ready/accept logic,
   one-entry valid state, reset handling, guarded outputs, terminal-order
   faulting, and the absence of a child-entity instantiation.
3. Reject an empty module identity with the documented owner diagnostic.

## Requirement traceability

- REQ-G2-002 — the owner specializes concrete RV32/RV64 retirement-record
  widths at elaboration time.
- REQ-G2-004 — the admitted sequential module emits deterministic strict VHDL
  for its typed state and output bindings.
- REQ-G2-010 — provides the bounded one-entry dispatch/retirement ownership
  primitive, including backpressure, ordered capture, and terminal faulting.
- NFR-G2-003 — emitted RV64 VHDL uses concrete selected widths without a
  runtime XLEN selection path.
- NFR-G2-011 — the named synchronous active-high reset domain, explicit state
  registers, stable occupied payload, and absence of a hidden legacy owner are
  represented by the sequential plan and emitted bindings.

## Evidence boundary

This is source-level sequential-plan and strict-VHDL-text evidence for a
single-record owner. It does not prove an integrated parcel frontend, matching
retirement receipts, architectural commit semantics, reset-cycle simulation,
register-file or memory updates, pipeline recovery, GHDL/Sail/riscv-formal/SBY
execution, RTL synthesis, or a qualified hardware-retirement claim.
