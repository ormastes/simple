# occurs_check never recursed, so infinite types were accepted silently

- **ID:** occurs_check_never_recurses_2026-08-17
- **Severity:** P1 (silent wrong acceptance, no diagnostic)
- **Status:** FIXED 2026-08-17
- **File:** `src/compiler/10.frontend/core/type_inference.spl`

## Defect

`occurs_check(var_id, type_id)` resolved the tag through the substitution
store, compared it to `var_id`, and then returned `false` for everything
else:

```
    # For complex types, would need to recurse into structure
    # For now, simple check is sufficient
    false
```

Because it never descended into composite tags, `unify_types` could return
`UNIFY_FAIL_OCCURS` only when a variable was unified with *itself*. Every
structural infinite type — `T = [T]`, `T = (T, i64)`, `T = fn() -> T`,
`T = Dict<T, i64>`, `T = Result<T, E>`, `T = Option<T>` — unified
**successfully** and bound a cyclic substitution. `type_subst_apply` then
follows that chain, so a downstream consumer can diverge, and there is no
diagnostic anywhere on the path.

## Why it was fixable here

The comment implied the structure was unavailable. It is not. Type tags are
flat `i64`s, but every composite tag in `types.spl` carries its component tags
in a side registry keyed off the tag's base (`TYPE_DICT_BASE`,
`TYPE_RESULT_BASE`, `TYPE_TUPLE_BASE`, `TYPE_ARRAY_GENERIC_BASE`,
`TYPE_OPTION_GENERIC_BASE`, `TYPE_UNION_BASE`, the reference/pointer/atomic/
weak/iso/exclusive wrappers, and `named_type_field_type_tags` for named
struct/class/enum types). All of it is reachable, and `type_inference.spl`
already imported one of those accessors.

## Fix

`occurs_check` now delegates to a bounded `occurs_check_depth` that dispatches
on tag range and recurses into every registered composite. A companion
`occurs_check_fn(var_id, param_tags, ret_tag)` covers function types, which
have no flat composite tag. Depth is bounded at `OCCURS_MAX_DEPTH = 64`;
exceeding the bound reports `true`, since a chain that deep is itself evidence
of an infinite type.

Missing exports for the tuple/union/named accessors were added to
`src/compiler/10.frontend/core/types.spl`.

## Second defect, found by the detection spec

The first version of the fix was wrong in a way the reproducer could not see.
`TYPE_VAR_BASE` is `50000`, which is **above** `TYPE_NAMED_BASE` (`10000`), so
the `resolved >= TYPE_NAMED_BASE` arm swallowed every unbound type variable and
descended into a bogus field-tag list — making `occurs_check` report `true` for
an unrelated variable. Only the "must not over-report" half of the detection
spec caught it (`Results: 24 total, 23 passed, 1 failed`). An explicit
`is_type_var(resolved)` leaf guard now precedes the composite dispatch.

This is the argument for the detection spec as a rule: the `T = [T]`
reproducer passes against a fix that special-cases arrays, and passes against
a fix that over-reports on every variable.

## Evidence

Spec: `test/01_unit/compiler/type_checker/occurs_check_structural_spec.spl`
(24 examples: 3 reproducer, 16 shape-coverage, 2 nesting/substitution,
3 over-report guards).

- Before the leaf guard: `Results: 24 total, 23 passed, 1 failed`
- After: `Results: 24 total, 24 passed, 0 failed`

The three reproducer examples are unsatisfiable against the old body by
construction — it returns a literal `false` on that path.

## Not proven

- No end-to-end evidence that a user-visible program previously diverged or
  miscompiled through this path. `type_inference.spl` is the bootstrap-subset
  HM engine; the richer structural unifier in
  `src/compiler/20.hir/inference/unify.spl:172` already had a correct
  recursive `occurs_check`, so the blast radius is limited to consumers of the
  flat-tag engine, which were not enumerated.
- `occurs_check_fn` has no in-tree caller yet; it is exercised only by the
  spec. Wiring it into function-type unification is follow-up work.
