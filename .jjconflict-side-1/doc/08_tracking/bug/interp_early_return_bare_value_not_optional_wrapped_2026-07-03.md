# Bug: early `return <bare-value>` inside a nested block is not Option-wrapped for `T?`-returning `impl` fns

**Date:** 2026-07-03
**Severity:** P2 — silent wrong-answer (returns `None` instead of `Some(value)`), previously
masked by a false-green spec
**Status:** Workaround applied in `atlas_builder.spl`; interpreter fix pending

## Summary

An `impl` method declared `-> T?` that does an **early return of a bare
(non-`nil`, non-`Option`) value from inside a nested `if`/`while` block**
returns `None` instead of `Some(value)`. Only the function's **trailing**
expression gets the implicit bare-value → `Some(...)` promotion; a `return`
statement nested inside a conditional block does not.

This is the mirror image of the already-tracked
`doc/08_tracking/bug/free_fn_optional_wrap_2026-06-26.md` (free fns
over-wrap into `Some`) and
`doc/08_tracking/bug/ds_utils_t_optional_wrapping_inconsistency_2026-06-26.md`
(same `impl` method wraps inconsistently depending on call context) — same
interpreter subsystem (return-value optional-wrapping), a different trigger
(early return from a nested block vs. trailing expression).

## Reproduction

```spl
struct Item:
    name: text
    x: i32

struct Box:
    items: [Item]

impl Box:
    fn find_v3(name: text) -> Item?:
        if self.items.len() > 0:
            if self.items[0].name == name:
                return self.items[0]   # bare value, nested return
        nil

    fn find_v4(name: text) -> Item?:
        var i = 0
        while i < self.items.len():
            if self.items[i].name == name:
                return Some(self.items[i])  # explicit Some — works
            i = i + 1
        None

val b = Box(items: [Item(name: "hero", x: 1)])
b.find_v3("hero")   # None  — WRONG, item exists
b.find_v4("hero")   # Some(Item(name: "hero", x: 1)) — correct
```

## Real-world instance found

`src/lib/nogc_sync_mut/engine/sprite/atlas_builder.spl`'s
`AtlasLayout.find_sprite(name)` used the broken `return self.sprites[i]`
shape. It always returned `None` for any name that was actually present —
100% broken, not intermittent — for every caller.

## Why it went undetected

`test/01_unit/lib/engine/atlas_builder_spec.spl`'s "packs a single sprite"
(and similar) tests call `find_sprite` and then assert fields **only inside
`if val Some(s) = sp:`** — when `find_sprite` wrongly returns `None`, the
`if` body (and every `expect()` inside it) never runs, and the test still
prints `✓` (false-green: an assertion inside an unreached branch proves
nothing). Only the dedicated "returns nil for missing sprite name" test
tracked a `found` boolean outside the `if`, and that one happened to expect
`false`, so it also passed vacuously.

## Fix applied (workaround)

`find_sprite` rewritten to use explicit `Some(self.sprites[i])` / `None`
instead of the bare early return / bare `nil`. Confirmed via minimal repro
above and via the CLI consumer (`src/app/spritesheet/main.spl` `pack`,
which composites pixels into an atlas PNG using `find_sprite` and would
silently emit an all-transparent atlas otherwise).

## Real fix needed

Interpreter: implicit bare-value → `Some(...)` / bare-`nil` → `None`
promotion for `-> T?` functions must apply uniformly to every `return`
statement in the function body, not just the trailing expression. Compare
with the free-function over-wrapping bug — likely the same code path
handles "is this the function's result value" detection inconsistently
between trailing-expression and early-`return` cases.

## Follow-up test debt

`test/01_unit/lib/engine/atlas_builder_spec.spl`'s positive-match tests
should track a `found` boolean the same way the negative-match test does,
so a regression back to this bug fails loudly instead of vacuously passing.
