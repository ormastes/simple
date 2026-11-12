# Seed Cranelift backend does not type-check cross-module call arguments (2026-11-12)

Status: open
Area: src/compiler_rust (seed cranelift backend) / bug p4p2_cranelift_verifier_types_2026-10-20

## Symptom

`test/02_integration/compiler/backend/cranelift_cross_module_call_abi_spec.spl`
builds two cranelift modules (provider + caller), links them with a C harness,
and runs them. The spec exists to guard bug `p4p2_cranelift_verifier_types_2026-10-20`:
the import signature for a cross-module call must come from the CALLEE's
declaration, not the caller's operands.

Under the Rust seed the bug reproduces — the fixture that passes an `i64`
where the callee declares `f64` is accepted and run instead of rejected:

```
✗ <case>
  expected int_to_f64 value=cv=1.500 rc=0 to contain
  arg 0 is i64 but the callee declares f64
```

i.e. `take_i64(2.0)` / `half_f64(3)`-style mismatches compile and execute
("silent garbage") rather than being diagnosed at build time.

## Root cause

The seed's cranelift backend does not apply the callee-declared parameter
types when importing a cross-module call (the exact defect the spec's header
describes for the pure-Simple side). The spec is behaving correctly — it is
catching a real, still-open defect in the seed backend.

## Unblock

Port/apply the verifier-types fix (callee-declared import signatures) to the
seed cranelift backend, or run this spec under the rebuilt pure-Simple
producer where the fix landed. Keep the spec RED until the mismatch is
diagnosed; do not weaken its assertions.
