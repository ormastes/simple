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

## PARTIALLY FIXED 2026-11-13 (wave-2 deep-fix lane, work/compiler-seed-deepfix-20261113)

Codec oracle updated (record-sanctioned): the canonical header legitimately
moved v4 -> v7 (`HIR_CANONICAL_CODEC_VERSION = "spl-hircodec-canonical-v7-
imported-layouts"`, src/compiler/20.hir/hir_codec.spl:51; v16 frames are
correctly rejected because they decode `imported_layouts` empty and raise a
spurious W-HIR-INFER-001). The spec oracle now pins v7 without a trailing
space — the version string carries a suffix, so `"spl-hircodec-canonical-v7 "`
(with space) can never match `"spl-hircodec-canonical-v7-imported-layouts ...
"`; the original v4 oracle only matched because v4-era version strings had no
suffix.

The two identity examples stay RED, with a precise diagnosis from a scratch
probe (since removed): the product admission logic IS present and correct on
paper — `resolve_builtin_collection_operation`
(src/compiler/35.semantics/perf_facts/builtin_collection.spl) classifies a
typed-Array receiver + one positional lambda arg as
`BuiltinCollection(ArrayMap)`, and the HIR interpreter backend
(src/compiler/70.backend/backend/interpreter_expr.spl:351) already executes
that identity. The probe showed, under the seed: the fixture's HIR Let carries
the declared `[i64]` type (backfill input is correct), the map receiver is
`NamedVar(sym = 1)` — the SAME symbol id as the Let — yet
`attach_inferred_type` attaches a NON-Array type ("other-kind") and resolution
stays Unresolved. So the quiet-mode `local_value_types` backfill
(resolve.spl:417 / resolve_lookup_helpers.spl:41) either misses the integer-
keyed Dict entry or the HirType aggregate corrupts when read back — a
seed-runtime aggregate/Dict transport divergence (the same class the triage
notes repeatedly flag as "seed aggregate typing not authoritative"), not a
missing product feature. Fixing it needs a seed-level Dict<i64, aggregate> or
HirType transport investigation beyond this lane; documented as remainder.
Spec stays RED per this record's instruction, now failing only the two
genuine identity assertions.
