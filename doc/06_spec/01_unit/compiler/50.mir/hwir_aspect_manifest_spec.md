# Typed HWIR Aspect Manifest Admission

**Executable companion:** `test/01_unit/compiler/50.mir/hwir_aspect_manifest_spec.spl`

## Purpose and scope

This focused unit specification admits only typed observational aspect
manifests with declared matches, valid effect-class proof obligations, and the
supported RTL `module.port` join point. It checks absent-plan zero cost,
manifest conflict and accounting diagnostics, and deterministic typed-HWIR
output-port attachment.

## Scenarios

1. Construct an absent plan and verify that it is diagnostic-free.
2. Admit a required observation only when it names a semantic HWIR node.
3. Reject missing, zero-match, conflicting, textual-advice, invalid-proof,
   accounting, scope, join-point, and stage declarations.
4. Attach one transparent observation to a lowered typed module and check its
   strict VHDL rendering contract.
5. Leave an absent plan unchanged and reject an undeclared probe.

## Requirement traceability

- REQ-FV2-011 — typed join points, introduced symbols, and weave identity are
  explicitly constrained.
- REQ-FV2-019 — invalid declaration and attachment boundaries fail closed.

## Evidence boundary

This is manifest admission and typed-module weaving evidence only. It does not
implement general aspect execution, prove the declared obligations, provide a
formal AOP closure, or qualify generated VHDL, GHDL, synthesis, or a deployed
hardware artifact.
