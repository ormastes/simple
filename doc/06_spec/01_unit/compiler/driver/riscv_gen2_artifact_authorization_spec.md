# RISC-V Gen2 Artifact Authorization

## Purpose

This focused unit specification protects existing compiler-owned Gen2 VHDL
bundles while product admission is rejected. Replacement is permitted only
after the typed product path has produced and authorized its emission receipt.

## Scenarios

1. Preserve VHDL, source-map, and manifest sidecars when an RV32 C.JAL product
   is invoked with a non-specialized target.
2. Preserve the complete prior bundle when critical assurance-policy admission
   fails.
3. Reject requested and woven AOP contamination before receipt authorization,
   retaining the complete prior bundle in each case.
4. Reject an API-level source closure mixed into a compiler-owned product,
   retaining the complete prior bundle before the receipt boundary.

## Requirement traceability

- REQ-G2-006 — critical policy admission.
- REQ-G2-009 — source-less compiler-owned product and AOP isolation.
- NFR-G2-010 — deterministic, fail-closed artifact provenance.

## Evidence status

The executable source is
`test/01_unit/compiler/driver/riscv_gen2_artifact_authorization_spec.spl`.
Bootstrap-seed execution is diagnostic only. Release evidence requires the
admitted self-hosted runtime and retained qualification receipt defined by the
Gen2 system-test plan.
