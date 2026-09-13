# unify_types: the occurs check is dead code, UNIFY_FAIL_OCCURS is unreachable

## Closed 2026-09-13 — fixed; the guard is now structural AND reachable, PROVED by running

**Status: CLOSED (fixed).** The entry's central claim — "`UNIFY_FAIL_OCCURS` is
never returned by `unify_types` for any input" — is now false, and the second
half of the complaint ("even if it were reachable it could not detect
`T = List<T>`, the case it exists to prevent") is also resolved.

### Source: the check is now structural

`src/compiler/10.frontend/core/type_inference.spl:97-164` no longer holds the
one-line `resolved == var_id` test. It is now `occurs_check` ->
`occurs_check_depth(var_id, type_id, 0)`, which recurses through the type
structure with an `OCCURS_MAX_DEPTH` bound (a cycle deeper than the bound is
itself treated as evidence of an infinite type):

- single-component wrappers: array-generic, option-generic, isolated,
  exclusive, reference, pointer, atomic, weak
- two-component composites: dict (key and value), result (ok and err)
- N-component: tuple elements, union members, and named struct/class/enum types
  via `named_type_field_type_tags`
- a separate `occurs_check_fn(var_id, param_tags, ret_tag)` catches
  `T = fn() -> T`, which has no flat composite tag in this registry

The `is_type_var(resolved) -> false` early-out is kept and commented as
load-bearing (TYPE_VAR_BASE 50000 sits above TYPE_NAMED_BASE 10000, so without
it an unbound variable would be misread as a named type).

### Empirical: all three verdicts are now reachable

Probe run against the real module on the Rust seed
`build/vt4/bootstrap/simple.exe` (`UNIFY_SUCCESS=0`, `UNIFY_FAIL_MISMATCH=1`,
`UNIFY_FAIL_OCCURS=2`):

```
1 self-array   occurs=true  unify=2      # v = [v]        -> OCCURS
2 plain-bind                unify=0      # w = text       -> SUCCESS
3 same-var                  unify=0      # x = x          -> SUCCESS
4 self-option  occurs=true  unify=2      # y = y?         -> OCCURS
5 mismatch                  unify=1      # text = bool    -> MISMATCH
6 self-dict-value occurs=true unify=2    # z = {text: z}  -> OCCURS
```

Rows 1, 4 and 6 are exactly the constructions the original entry listed as
returning SUCCESS. They now return `UNIFY_FAIL_OCCURS`, through three different
composite shapes (single-component wrapper, another single-component wrapper,
and the value slot of a two-component composite) — so this is the recursion
working, not a special case for arrays. Rows 2, 3 and 5 confirm the guard did
not become trigger-happy: ordinary binding, self-unification and a genuine
mismatch still return their own verdicts.

MEASURED, not inferred. The fixing commit was not bisected.

### The spec-vacuity half is NOT fixed — and the body below is wrong about it

Measured 2026-09-13, **both** copies still carry 70 `it` blocks, 70
`expect true` placeholders and **zero** `use` lines:

- `test/01_unit/compiler/type_checker/type_inference_v2_spec.spl`
- `test/01_unit/lib/std/type_checker/type_inference_v2_spec.spl`

So the sentence further down — "the import works fine and is used by the
repaired spec" — does not describe the tree at HEAD. Whatever repaired copy
existed was never landed, or was landed and later reverted. The unifier is
still covered by no executing assertion, which is why the occurs-check fix
above had to be proved with an ad-hoc probe instead of by running the spec.

This is a live defect, not history — but it is **not** the mechanical fix it
looks like, and that is worth recording so the next person does not start it
expecting a 30-minute job. The spec's header points its assertions at
`src/lib/std/src/type_checker/type_inference_v2.spl`, which **does not exist**;
the only `type_inference_v2.spl` in the tree is
`src/compiler_rust/lib/std/src/type_checker/type_inference_v2.spl`, inside the
seed's vendored std copy. The engine that is actually live and that the
occurs-check fix above landed in is a *different* module,
`compiler.core.type_inference`. So de-vacuifying requires first deciding which
implementation the 70 examples are meant to cover and retargeting them — a
scoping decision, not a text substitution. The `it` names themselves
(`unifies Int with Int`, `fails to unify Int with Bool`, `unifies type variable
with Int`, ...) do map cleanly onto the `compiler.core.type_inference` API
exercised in the probe above, which is the obvious target if someone picks
this up.


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
