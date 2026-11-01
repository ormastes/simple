# HmInferContext.unify: no arm for Union / Isolated / Projection, identical unions report Mismatch

**Status: CLOSED (fixed 2026-11-01).** Lane: generics-coverage-mcdc, bug-fix
sub-lane `work/fix-unify-union-arm-20261101`.

## Symptom

`src/compiler/30.types/type_infer/core.spl` `unify` matched on
`(ty1.kind, ty2.kind)` with arms for primitives, `Infer`, `Function`, `Tuple`,
`Array`, `Slice`, `Dict`, `Optional`, `Result`, `Ref`/`Ptr`, the no-GC sigils,
`Named`, `TypeParam`, `Tensor` and `Layer`, then `case _: Mismatch`. There was
no arm for `Union`, `Isolated` or `Projection`, so:

- two structurally identical `Union[i64, str]` values returned
  `TypeInferError.Mismatch`;
- `iso T` against `iso T` returned Mismatch;
- `T.Item` against `T.Item` returned Mismatch;
- an inference variable hidden inside any of those carriers
  (`Union[?a, str]` vs `Union[i64, str]`) could never be bound by unification,
  even though packet E2 (commit `178ecc247f1`) had already taught
  `Substitution.apply`, `occurs` and `collect_free_vars` to walk the same
  carriers.

## Discovery

MC/DC driver `test/01_unit/compiler/type_infer/coverage/core_mcdc_spec.spl`
(generics-cov lane), spec `core.spl:234 Union self-unify should succeed`
(`@tag:bug-suspect`, REQ-GEN-COV-CORE-059): the decision inventory showed the
`case _` Mismatch arm as the only reachable outcome for a Union pair.

## Fix

`unify` gained three arms, placed after `TypeParam` and before `Tensor`:

- `(Union(m1), Union(m2)) if m1.len() == m2.len()`: member-wise unification by
  index; the first failing member's error is returned.
- `(Isolated(i1), Isolated(i2))`: unify the inner types. `iso T` vs bare `T`
  still falls through to Mismatch, consistent with the `Unique`/`Shared`/`Weak`
  sigil arms.
- `(Projection(b1, n1), Projection(b2, n2)) if n1 == n2`: unify the bases;
  differing associated names fall through to Mismatch.

### Ordering choice for Union: positional, not order-insensitive

Union unification is POSITIONAL (same arity, same member order). Reasons:

1. Every other consumer is positional: `hir_type_lists_equal` in
   `src/compiler/20.hir/hir_lowering/type_equality.spl`, the HIR-level unifier
   `src/compiler/20.hir/inference/unify.spl` (`case (Union(types1), Union(types2))`),
   `Substitution.apply` and `HmInferContext.occurs`.
2. HIR lowering (`hir_lowering/types.spl`, `d_union` branch) preserves source
   member order and does not sort or dedupe, so `A | B` and `B | A` are
   already distinct `HirType` values everywhere else in the pipeline.
3. An order-insensitive match is ambiguous once a member is an unbound
   inference variable (`Union[?a, i64]` vs `Union[i64, str]`: does `?a` bind
   `str` or `i64`?). Resolving that needs trial unification with substitution
   rollback, which the HM kernel does not have and which this fix does not
   introduce.

If canonical (sorted) union ordering is ever wanted, it belongs in HIR
lowering so that all consumers agree, not in `unify` alone.

### Out of scope (deliberately not added)

The HIR-level unifier also accepts a concrete type against a union that
contains it (subsumption). The HM kernel's `unify` is an equality relation and
`Union[i64, str]` vs `i64` still reports Mismatch; the regression spec pins
that behaviour so any future subsumption change is explicit.

## Regression spec

`test/01_unit/compiler/type_infer/unify_union_regression_spec.spl`
(REQ-COMPILER-TYPE-INFER-001): identical unions unify; different-member,
different-arity and reordered unions mismatch; `Union[?a, str]` vs
`Union[i64, str]` binds `?a = i64`; bare `?a` binds the whole union; `?a` vs
`Union[?a, str]` fails the occurs check; plus the Isolated and Projection
unify / bind / mismatch cases.

## Coordination

Packet E2 (`work/e2-hm-traversal`, landed as `178ecc247f1`) owns the carrier
walks in `occurs`, `Substitution.apply` and `collect_free_vars`. This fix only
touches the `unify` match in `core.spl` and does not alter those functions or
generalization.
