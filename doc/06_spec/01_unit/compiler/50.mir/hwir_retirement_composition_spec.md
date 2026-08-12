# RISC-V Gen2 Retirement Receipt Composition

## Purpose

This unit specification freezes the typed elaboration boundary between the
single-outstanding parcel frontend and a future architectural retirement
producer. It validates wiring and identity contracts; it does not emit a child
implementation or prove an architectural commit.

## Scenarios

1. Bind RV32 and RV64 frontend and producer contracts to one shared reset and
   exact dispatch/receipt identity widths.
2. Reject a producer with a renamed reset or a shortened lineage receipt.
3. Reject omitted or rewired closed receipt bindings before composition.
4. Reject a substituted legacy child route before it can be bound.

## Requirement traceability

- REQ-G2-010 — one-entry dispatch and matching retirement contract.
- NFR-G2-006 — critical fail-closed boundary.
- NFR-G2-011 — explicit synchronous reset and typed state/identity widths.

## Evidence status

The executable source is
`test/01_unit/compiler/50.mir/hwir_retirement_composition_spec.spl`.
This is elaboration-boundary evidence only. A typed architectural commit owner,
generated RTL, and self-hosted GHDL receipt remain required for retirement
integration.
