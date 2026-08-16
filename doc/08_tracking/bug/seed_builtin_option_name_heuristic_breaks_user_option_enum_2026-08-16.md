# Seed HIR lowering: the builtin-`Option` exception is keyed on a NAME, so a user-declared `enum Option` is misrouted

**Status:** open
**Found:** 2026-08-16, structural review of `8d96687c991` on `origin/main`
**Severity:** high — silently reintroduces an irrefutable-pattern bug that a prior fix was written to close
**Component:** Rust seed, `hir/lower` (both the expression and statement match-lowering twins)

## Summary

Commit `8d96687c991` ("fix(seed): match builtin Option None in HIR lowering") added an exception so
that the builtin `Option<T>` — which registers as a `HirType::Enum` named `"Option"` but whose runtime
representation is nil-boxing — takes the optional-shaped fast paths instead of the enum-discriminant
path. The fix is correct for the builtin. But it identifies the builtin by **name string**, while the
runtime identifies it by **reserved enum id**. A *user-declared* `enum Option` matches the name test
and gets misrouted onto the nil-boxing path, where its patterns become irrefutable.

This is not a hypothetical collision: the shape is declared in-tree, in the very regression test the
earlier fix exists to satisfy.

## The mismatch

The new predicate, identical in `hir/lower/expr/control.rs` and `hir/lower/stmt_lowering.rs`:

```rust
let subject_is_builtin_option = matches!(
    self.module.types.get(subject_ty),
    Some(HirType::Enum { name, variants, .. })
        if name == "Option"
            && variants.len() == 2
            && variants.iter().any(|(n, p)| n == "Some" && p.is_some())
            && variants.iter().any(|(n, p)| n == "None" && p.is_none())
);
let subject_enum_owns_variant = !subject_is_builtin_option && matches!(/* … */);
```

Both runtimes gate the enum half of the check on a **reserved id**, never on the name:

- `src/compiler_rust/runtime/src/value/objects.rs:490` — `rt_is_none` is true for nil, or for
  `enum_id == OPTION_ENUM_ID` (reserved id 1) with `discriminant == hash("None")`.
  `rt_is_some` (`:505`) is exactly `!rt_is_none(value)`.
- `src/runtime/simple_core/core_values.spl:61` — the pure-Simple twin: `if rt_enum_id(value) != 1: return 0`.

A user-declared `enum Option` is allocated an ordinary enum id. It is never id 1.

## Failure mode

For a user-declared `enum Option: Some(i64); None`, `subject_is_builtin_option` is true, so
`subject_enum_owns_variant` is false and lowering takes the early returns at
`hir/lower/expr/control.rs:625-643`:

- `case Option::Some(v)` → `rt_is_some(obj)` → `!rt_is_none(obj)`. The object is not nil and its
  `enum_id != 1`, so `rt_is_none` is false and **`rt_is_some` is always true — the arm is
  irrefutable**. Worse, the early `return` fires before `nested_payload_condition` further down, so
  the payload sub-pattern binding `v` is **discarded outright**.
- `case Option::None` → `rt_is_none(obj)` → `enum_id != 1` → **always false; the arm never matches.**

That is verbatim the failure the pre-existing comment in `stmt_lowering.rs` records as the reason
`subject_enum_owns_variant` was introduced in the first place — *"which made `case Some(x)`
irrefutable and bound x = 3"*. The new exception re-opens it for any enum named `Option` of that shape.

## Reachable in-tree

- `src/compiler_rust/driver/tests/runner_tests.rs:851,870` — `runner_handles_option_type` declares
  exactly `enum Option: Some(i64); None` and asserts `42` then `99`. The `99` case
  (`let x = Option::None`) is tested against the `Some(v)` arm first, which is now irrefutable.
- `src/compiler_rust/driver/tests/runner_tests.rs:892` — `runner_handles_option_type_functions`, same shape.
- `src/compiler/30.types/bidirectional_types.spl:105` — the self-hosted compiler's own type system
  declares `enum Option<T>`.
- `src/compiler_rust/lib/std/src/core/option.spl:4` — stdlib `enum Option<T>`; here the misrouting is
  presumably intended, since this declaration *is* the builtin, but it is matched by the same name
  test rather than by identity, so the intent is not expressed.

## Suggested direction (not applied)

Key the predicate on the same identity the runtime uses — the reserved `OPTION_ENUM_ID` — rather than
on `name == "Option"`, so compile-time and runtime agree on what "builtin Option" means. If the
`TypeId`/`HirType` layer does not carry the reserved id at that point, the id should be threaded to
where the decision is made; matching on a user-ownable name string cannot be made correct, because a
user enum is allowed to have that name and that shape.

Secondary, from the same review: the ~14-line predicate is duplicated verbatim across the two twins,
held in sync only by a comment. Whatever the fix, it wants to be one shared helper — the duplication
is what will let the two drift.

## Evidence and limits

Source trace only. No test was executed: this lane's evidence rule requires pure-Simple self-hosted
execution and forbids Rust seed test results, and in any case no working self-hosted binary exists on
this machine — see
`stage3_native_build_segv_two_distinct_faults_tagged_value_seam_2026-08-11.md`, which records a
fleet-wide sweep finding all five self-hosted artifacts non-functional. The claim here rests on
reading the lowering predicate, the two early-return branches it selects, and both runtime
implementations of `rt_is_none`/`rt_is_some`; each is cited by file and line above. **Running
`runner_handles_option_type` against a rebuilt seed would confirm or refute it in one step** and is
the recommended next action for whoever owns the seed.
