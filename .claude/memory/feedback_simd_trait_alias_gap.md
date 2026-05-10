# SIMD Trait Alias Resolution Gap (D3 type-IR)

## Symptom
`semantic: method 'add' not found on type 'Vec4f'` (and mul, fma, lane,
set_lane, reduce_sum, reduce_max, shr_logical, shr_arith, lanes, cmp_lt).

Affects: any call to trait-impl methods on a type alias.
Example: `Vec4f.add(vb)` where `Vec4f = FixedVec<f32,4>` (aliases.spl)
and `add` is defined in `impl FixedVec with Vector` (fixed.spl line ~44).

## Root Cause
The interpreter's method-resolution does not expand type aliases before
looking up trait impl blocks. When `Vec4f` is declared as
`type Vec4f = FixedVec<f32,4>`, calls to `v.add(vb)` (where `v: Vec4f`)
fail because the interpreter looks for `add` on `Vec4f` directly, not on
the expanded `FixedVec<f32,4>`. Static methods like `splat()` and
`from_array()` DO work through the alias (they are found via a different
path — likely the concrete `impl FixedVec` block, not the trait impl block).

## Affected Tests (D5 kickoff)
- fixed_spec.spl: F-03..F-08, F-10 (7 tests)
- vector_spec.spl: V-01, V-02 (2 tests)
- mask_spec.spl: M-03, M-04, M-05 likely (depend on cmp_lt, mask_select)
- scalable_spec.spl: S-01 lanes() call

## Fix Owner
D3 (type IR). The type-alias expansion pass must resolve aliases before
trait impl method lookup in the interpreter's semantic phase.
File: src/compiler/ (30.types or type resolution layer).

## Separate Parse Issue
`Generic<X>.method()` also fails at parse: "expected expression, found Dot".
Workaround: use deprecated `::` syntax — `Mask<Vec4f>::all_ones_n(4)`.
This is a parser limitation, separate from the trait-alias semantic gap.
Applies to: mask_spec.spl, scalable_spec.spl (static calls on Mask<V> and
ScalableVec<T> with explicit type parameter).

## Discovered
2026-05-02 by D5 agent during test scaffolding.
