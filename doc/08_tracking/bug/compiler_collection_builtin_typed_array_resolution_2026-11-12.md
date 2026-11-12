# Typed `Array.map` is not resolved to the builtin-array-map operation (2026-11-12)

Status: open
Area: src/compiler (builtin method resolution / HIR codec provenance)

## Symptom

`test/02_integration/compiler/collection_builtin_resolution_spec.spl` (3
examples, 2 failing under the seed on release/1.0.0):

```
✗ should retain a resolved operation identity for a typed Array map
  expected unresolved-or-user-method to equal builtin-array-map
  expected spl-hircodec-canonical-v6-local-annotation-provenance
    spl-flatpool-v15-unit-decl-legacy-origin
    to start with spl-hircodec-canonical-v4
```

Expected: a typed `Array` `map` call resolves to the `builtin-array-map`
operation and records a `spl-hircodec-canonical-v4...` provenance tag.
Actual: the resolution reports `untyped` / `unresolved-or-user-method`, and the
provenance tag is the newer `...-canonical-v6-...` /
`spl-flatpool-v15-...` form rather than the `v4` prefix the spec pins.

## Root cause

The compiler's builtin-method resolution for a typed `Array.map` does not
classify the call as `builtin-array-map` on this path, and the HIR codec
provenance version has moved past the `v4` tag the spec asserts. Either the
spec encodes a desired contract not yet implemented, or resolution/provenance
regressed.

## Unblock

Confirm the intended builtin-resolution contract and codec provenance version.
If the `v6`/`v15` provenance and the current resolution are correct, update the
spec oracle; if resolution is genuinely missing, implement typed-`Array` map
classification. Until then leave the example RED (do not weaken it to pass).
