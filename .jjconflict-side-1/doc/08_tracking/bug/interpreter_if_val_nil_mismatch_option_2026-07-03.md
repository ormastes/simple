# Interpreter `if val x = <nil Option>:` Wrongly Takes the Match Branch - 2026-07-03

Status: SOURCE FIXED (2026-07-15); executable interpreter proof pending a
runnable pure-Simple compiler artifact.

## Symptom

`if val x = expr:` (the language's `if let`-equivalent pattern-binding form,
see `.claude/rules/language.md`) is supposed to take the true branch only when
`expr` (an `Option<T>`) is non-nil. Under this project's interpreter-fallback
execution path, it incorrectly takes the true branch even when `expr` is
genuinely `nil`.

Minimal repro (`describe`/`it` context, run via `bin/simple test`/`bin/simple run`):

```simple
use std.spec

fn maybe_none() -> Option<i64>:
    nil

describe "if val nil handling":
    it "does not match on nil":
        val v = maybe_none()
        var matched = false
        if val x = v:
            matched = true
        assert_false(matched)   # FAILS: matched == true
```

`v == nil` correctly evaluates to `true` right before the `if val` check (so
the underlying Option value is genuinely nil) — only the `if val` pattern
match misfires. A plain `if expr != nil:` check on the same value is correct
in the same run.

## Where it bites

Reproduced with both a plain `Option<i64>` and the engine's
`collide_circle_aabb(...) -> Option<Contact2D>`
(`src/lib/nogc_sync_mut/engine/physics/collision2d.spl`) returning `nil` for a
circle and box far apart — `if val _ = contact:`/`if val c = contact:` both
wrongly entered the true branch.

Confirmed this is specific to the **interpreter fallback** path: files that
trigger "JIT compilation failed, falling back to interpreter" (e.g. an
unrelated HIR lowering error elsewhere in the same file) exhibit the bug;
JIT-compiled call sites elsewhere in the codebase using the same
`if val c = collide_pair(...):`/`if val c = result:` idiom (e.g.
`src/lib/nogc_sync_mut/engine/physics/world.spl`) are not known to be
affected — those specs (`physics_3d_collision_spec.spl`, etc.) pass.

## Impact / workaround

Hit while wiring `game.breakout` onto `engine.physics.collision2d` for P1 of
`doc/03_plan/app/game_platform/game_platform_master_plan.md` (breakout's
`fixed_update` runs under the interpreter fallback because
`test/03_system/game2d/breakout_event_animation_spec.spl`'s own
`kill_all_but_first` helper fails HIR lowering — "mutation without mut
capability" — which forces the whole file onto the interpreter path).

Workaround applied in `src/app/game.breakout/game.spl`
(`_update_ball_paddle`/`_update_ball_bricks`): use `contact != nil` instead of
`if val _ = contact:`/`if val c = contact:` to detect a collision. This is
correct (verified via the repro above) and does not require the contact's
fields, since breakout keeps its own bounce/deflection response math.

## Suggested fix direction (not investigated further)

Compare interpreter-mode lowering/evaluation of `if val` pattern-binding
against the JIT path's handling of the same node — the JIT path (or whatever
lowering `world.spl`'s passing specs exercise) evidently distinguishes
`Some`/`nil` correctly; the plain tree-walking interpreter fallback does not.

## Resolution

Plain `if val`/`while val` desugars now mark their synthetic binding for
Option-only normalization. The interpreter maps `Option::None` to nil and
`Option::Some` to its payload while preserving Result wrappers and ordinary
empty text/arrays. The explicit `.?` operator keeps its broader not-empty
semantics. Mirrored interpreter system tests cover statement, expression,
while, Result, and ordinary-empty-value forms.
