# Matching a user-declared enum named `Option`

Simple has a builtin `Option<T>`, and it also lets you declare your own enum
called `Option`. These are **not** the same thing at runtime, and match lowering
has to keep them apart. This page explains how they differ and what breaks when
the distinction is drawn on the wrong property.

## Two representations

| | Builtin `Option<T>` | User-declared `enum Option` |
|---|---|---|
| Runtime shape | nil-boxing — `None` is the nil sentinel, `Some(x)` a boxed optional | an ordinary allocated enum object |
| Identity | a **reserved enum id** (`OPTION_ENUM_ID`, value `1`) | an ordinary, dynamically assigned enum id |
| Match strategy | optional-shaped fast path (`rt_is_none` / `rt_is_some`) | discriminant path (`rt_enum_check_discriminant`) |

Both register as a `HirType::Enum` named `"Option"` owning `Some`/`None`. The
name alone therefore cannot tell you which one you have.

## The runtime is the authority

Both runtime implementations agree, and both key on the **id**, never the name:

```rust
// src/compiler_rust/runtime/src/value/objects.rs:490
pub extern "C" fn rt_is_none(value: RuntimeValue) -> bool {
    // … nil checks …
    get_typed_ptr::<RuntimeEnum>(value, HeapObjectType::Enum)
        .is_some_and(|p| unsafe {
            (*p).enum_id == OPTION_ENUM_ID && (*p).discriminant == none_disc
        })
}
```

```
# src/runtime/simple_core/core_values.spl:61
pub fn rt_is_none(value: i64) -> i8:
    if value == 3:
        return 1
    if rt_enum_id(value) != 1:
        return 0
    return if rt_enum_discriminant(value) == 1: 1 else: 0
```

`rt_is_some` is exactly `!rt_is_none` in both.

## What goes wrong if lowering keys on the name

Send a user-declared `enum Option: Some(i64); None` down the optional fast path
and both arms break, in opposite directions:

- **`case Option::Some(v)` becomes irrefutable.** It lowers to `rt_is_some(obj)`.
  The object is not nil and its `enum_id != 1`, so `rt_is_none` is false and
  `rt_is_some` is unconditionally **true** — the arm matches a `None` value.
  Worse, that lowering returns early, before payload sub-pattern handling, so
  the binding `v` is silently **discarded**.
- **`case Option::None` never matches.** It lowers to `rt_is_none(obj)`, which
  checks `enum_id == 1` and is always **false** for a user enum.

Net effect: `None` values fall into the `Some` arm with an unbound payload.

This is not hypothetical. It is the failure the `subject_enum_owns_variant`
predicate exists to prevent — its own comment records the original symptom as
*"made `case Some(x)` irrefutable and bound x = 3"* — and it was reintroduced by
keying the builtin exception on `name == "Option"`. Tracked in
`doc/08_tracking/bug/seed_builtin_option_name_heuristic_breaks_user_option_enum_2026-08-16.md`.

## Rule for anyone editing match lowering

**Identify the builtin by the reserved enum id, not by the name string.** A user
enum is allowed to have the name `Option` and the shape `Some(T)`/`None`; a name
test cannot be made correct, only narrowed. If the id is not available at the
point of decision, thread it there.

The predicate exists in **two** places that must agree —
`hir/lower/expr/control.rs` (expression form) and `hir/lower/stmt_lowering.rs`
(statement form). They are currently duplicated verbatim and held in sync only
by a comment. Change both, and prefer factoring them into one helper.

## Why the interpreter will not catch this

The tree-walk interpreter binds match arms from `HirFunction` directly and never
consults the nil-boxing path, so an interpreted run reports green against a
broken compiler. **Any fence for this class must be a native lane.**

## Coverage

`test/03_system/compiler/user_option_enum_match_lowering_system_spec.spl`, with
its fixture at `test/fixtures/user_option_enum_match/main.spl`. It is
fail-closed and currently unexecuted — it requires a qualified pure-Simple
runtime, and none exists on the reference machine. See
`doc/03_plan/sys_test/engine2d_font_offload_fallback_system_lane.md`.
