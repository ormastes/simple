# RISC-V Gen2 Strict HWIR Host Evaluator

## Purpose

This unit specification executes the exact validated combinational HWIR graph
used by strict VHDL emission. It supplies a host-side oracle seam for composed
frontend tests without substituting an unrelated compressed-instruction
classifier.

## Scenarios

1. Execute the concrete RV32 and RV64 target-trap graphs for C.EBREAK and
   verify the original parcel, canonical instruction, PC progression, redirect,
   and precise breakpoint trap tuple.
2. Execute an unsupported parcel through the same composed graph and verify its
   illegal fallthrough tuple with no redirect or trap.
3. Reject missing or output-port inputs before graph execution.
4. Reject empty and duplicate declared-input tuples before the graph can produce
   a value.
5. Normalize narrow input values and execute both equality results and both mux
   choices through the prepared strict graph.
6. Reject unsupported operations, mismatched operation widths, and unreadable
   self-referential operands at typed graph preparation rather than attempting
   a partial evaluation. Strict graph ownership makes a schedulable
   multi-operation cycle unconstructible because only input ports are readable.

## Requirement traceability

- REQ-G2-001 — typed, closed interface validation.
- REQ-G2-010 — typed target-trap frontend composition.
- REQ-G2-011 — normalized legal/illegal outcome behavior.
- NFR-G2-002 and NFR-G2-012 — stable fail-closed diagnostics and deterministic
  composition semantics.

## Evidence status

The executable source is
`test/01_unit/compiler/50.mir/hwir_host_evaluator_spec.spl`. It is an
independent compiler-host oracle; it does not replace the required admitted
self-hosted generated-VHDL/GHDL receipt or architectural retirement proof.
