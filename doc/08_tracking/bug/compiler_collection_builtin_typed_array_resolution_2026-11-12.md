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

## FIXED 2026-11-13 (work/compiler-seed-remainders-20261113) -- diagnosis corrected

Wave-2's seed-transport hypothesis was disproven by probe; the real defect
was product logic, in two parts, both now fixed. All three examples pass
under the seed (2/3 before, with both failures in the identity examples).

1. `MethodResolver.resolve_module` (resolve.spl) gated the entire
   function-body walk on `module.impls.len() > 0 or module.classes.len() >
   0`, reusing the original functions dict otherwise. The gate's own
   justification (cycle-132: the rebuild is a field-identical copy when no
   method candidates exist) is false in quiet mode: the quiet walk's whole
   purpose is side effects that need no candidates -- the Let
   `local_value_types` backfill, receiver `attach_inferred_type`, and the
   candidate-free builtin collection admission. A bare
   `val items: [i64] = ...; items.map(\x: ...)` module has neither impls
   nor classes, so the walk never ran (probe: `lvt_keys=0` after
   `resolve_methods_quiet`), the receiver kept its lowering-attached type,
   and resolution stayed Unresolved. Probe evidence: plain
   `Dict<i64, HirType>` round-trips are CLEAN under the seed (no transport
   divergence); the receiver's non-Array type came from lowering, not from
   any resolve attach. Fix: the gate now also walks when `self.quiet`.

2. With the walk enabled, example 3 (HIR-interpreter execution) still
   failed: main returned `Value.Nil`. Two more bounded fixes:
   - `resolve_block` rebuilt `HirBlock` WITHOUT the `has` field, so every
     resolved block reported has=false and `eval_block` (interpreter.spl)
     never evaluated the trailing expression. It now carries
     `has` (and `unsafe_caps`, mirroring aspect_weave.spl / infer.spl).
   - Even unresolved single-file blocks expose a deeper seed-lane shape:
     lowering leaves the tail in the last Expr STATEMENT with has=false
     (the HirBlock.has/value aggregate stores drop on the interpreted
     lane; probe: lowered `fn main(): 5` -> has=false stmts=1). Simple
     blocks yield their tail expression, so `eval_block` now falls back to
     the last Expr statement's value when `has` is absent, using the
     discriminant-scalar idiom (sound on the stage4 lane, where the Expr
     pattern arm is always-true struct-shadowed).

Evidence (seed binary): example 1 identity `builtin-array-map` + v7
codec round-trip PASS; example 2 user-method exclusion PASS; example 3
interpreter returns Value.Int(5) for map and Value.Int(2) for filter
(probe parity with the spec oracle).

Deeper remainders: (a) the quiet walk on a manually constructed
`MethodResolver` (create_method_resolver + field set + resolve_module in
one caller) segfaults the seed interpreter on tiny modules -- the
production `resolve_methods_quiet` entry is clean; a minimal repro is
preserved in the lane's probe notes. (b) The seed's dropped-store class on
single-file `main` blocks is worked around at the consumer (eval_block)
rather than repaired in lowering transport. (c) Re-dumping a resolved
module's functions twice in one process crashed the probe harness once
(cycle-132 class); the spec path is unaffected.
