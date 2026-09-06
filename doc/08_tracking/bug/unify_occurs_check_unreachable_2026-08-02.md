# unify_types: the occurs check is dead code, UNIFY_FAIL_OCCURS is unreachable

- **Date:** 2026-08-02
- **Status:** OPEN
- **Severity:** HIGH — the type checker has no working guard against infinite
  types. The guard exists in source and can never fire.
- **Found by:** de-vacuifying `type_inference_v2_spec.spl`, whose 70 examples
  were all `expect true  # Placeholder until module import works`.
- **Component:** `src/compiler/10.frontend/core/type_inference.spl`

## Claim

`UNIFY_FAIL_OCCURS` is never returned by `unify_types` for any input.
PROVED by argument below and confirmed empirically.

## Mechanism — PROVED

`unify_types` resolves both operands through the substitution before comparing:

```
fn unify_types(type1: i64, type2: i64) -> i64:
    val t1 = type_subst_apply(type1)
    val t2 = type_subst_apply(type2)
    if t1 == t2:
        return UNIFY_SUCCESS          # <-- Case 1
    if is_type_var(t1):
        if occurs_check(t1, t2):      # <-- can never be true
            return UNIFY_FAIL_OCCURS
        ...
```

and `occurs_check` is:

```
fn occurs_check(var_id: i64, type_id: i64) -> bool:
    val resolved = type_subst_apply(type_id)
    if resolved == var_id:
        return true
    false
```

`t2` has already been through `type_subst_apply`, and `type_subst_apply` is
idempotent, so `occurs_check(t1, t2)` reduces to `t2 == t1`. That condition is
exactly Case 1, which already returned `UNIFY_SUCCESS` several lines earlier.
The occurs branch is therefore unreachable for every possible input.

The check is also acknowledged in-source as non-structural:

```
# For complex types, would need to recurse into structure
# For now, simple check is sufficient
```

So even if it were reachable it could not detect `T = List<T>`, the case it
exists to prevent. Both halves of the guard are missing: it does not recurse,
and it cannot fire.

## Empirical confirmation — PROVED

Every construction that should trigger an occurs failure returns
`UNIFY_SUCCESS`:

| construction | result |
|---|---|
| `unify_types(v, v)` | SUCCESS |
| `unify_bind(v1, v2)` then `unify_types(v1, v2)` | SUCCESS |
| chain `v1 -> v2 -> v3` then `unify_types(v1, v3)` | SUCCESS |
| `unify_types(v, TYPE_ARRAY_ANY)` | SUCCESS |
| `occurs_check(v, TYPE_ARRAY_ANY / TYPE_FN / TYPE_STRUCT)` | false |

No input was found that yields `UNIFY_FAIL_OCCURS`. INFERRED, not proved: that
no such input exists at all — the argument above says none does, but the claim
rests on that argument rather than exhaustive search.

## Why this went unnoticed — PROVED

`type_inference_v2_spec.spl` carried 70 examples, every one of them:

```
it "represents Int type":
    expect true  # Placeholder until module import works
```

The file imported nothing at all, so the engine was never called. The comment
blames a broken import; the import works fine and is used by the repaired spec.
70 examples reported green while covering none of the unifier.

Proof the old file could not detect a unifier regression, sabotaging the shipped
`type_subst_apply` so it stops following the substitution chain:

| | clean impl | sabotaged impl |
|---|---|---|
| **pristine spec (70 placeholders)** | GREEN | **GREEN, 0 failures** |
| **repaired spec (27 examples)** | GREEN | **RED, 2 failures** |

Control `rvv_misc_spec.spl` stayed GREEN throughout; restoring returned the
repaired spec to GREEN.

## Fix required

1. Order the checks so the occurs branch is reachable: test `occurs_check`
   against the *unresolved* operand, or compare structurally before collapsing
   `t1 == t2`.
2. Make `occurs_check` recurse into composite types (array element, function
   parameter and return, struct fields) so `T = List<T>` is actually caught.
3. Then add the `UNIFY_FAIL_OCCURS` example to `type_inference_v2_spec.spl`.
   It is deliberately absent today and the spec says why, so that a passing
   example does not enshrine the broken behaviour.

## Note on the repaired spec

`type_inference_v2_spec.spl` now has 27 examples driving the shipped module and
no placeholders. It deliberately does **not** assert the current occurs-check
behaviour. Asserting it would lock in the defect; leaving a placeholder would
recreate the vacuity. The gap is tracked here instead.

## Related

- `doc/08_tracking/bug/vacuous_spec_corpus_census_and_inert_assertion_forms_2026-08-02.md`
- `doc/08_tracking/bug/gc_analysis_desugar_dropped_method_bodies_2026-08-02.md`
