# Standalone Typed Sequential HWIR

**Executable companion:** `test/01_unit/compiler/50.mir/hwir_standalone_sequential_spec.spl`

## Purpose and scope

This focused source-level unit specification validates a standalone typed
ready-register sequential plan. It checks that a plan with explicit reset,
typed registers, rules, outputs, and no child identity renders as its own VHDL
entity; it also rejects residual child pins.

## Scenarios

1. Render a standalone ready-register plan and inspect its ready/data output
   logic without an instantiated child.
2. Add a child pin to the standalone plan and require the typed diagnostic.

## Requirement traceability

- REQ-G2-010 — the first bounded sequential Gen2 lane has an explicit reset
  domain, typed state, and an owned sequential plan.

## Evidence boundary

This is a source-level standalone-plan and VHDL-text unit test. It does not
execute a frontend/retirement protocol, prove cycle behavior, run RTL
simulation or formal checks, synthesize hardware, or establish a deployment
qualification claim.
