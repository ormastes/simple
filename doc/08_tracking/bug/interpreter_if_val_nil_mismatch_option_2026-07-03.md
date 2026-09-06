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

## Re-reproduction attempt 2026-09-06 — NOT REPRODUCIBLE on the current seed

Host: `bin/release/aarch64-unknown-linux-gnu/simple`, 50093192 bytes,
mtime 2026-09-06 09:59 (aarch64 Linux), `SIMPLE_EXECUTION_MODE=interpret` —
i.e. exactly the "interpreter fallback" lane this record isolates.

Fixture (`build/wi/r_ifval.spl`), the record's own repro plus a positive
control so a "never takes the branch" regression could not read as a pass:

```simple
fn maybe_none() -> Option<i64>:
    nil

fn maybe_some() -> Option<i64>:
    7

fn main() -> void:
    val v = maybe_none()
    var matched = false
    if val x = v:
        matched = true
    print("nil case matched={matched} (expected false)")

    val w = maybe_some()
    var matched2 = false
    var seen = 0
    if val y = w:
        matched2 = true
        seen = y
    print("some case matched={matched2} seen={seen} (expected true 7)")
```

Observed:

```
nil case matched=false (expected false)
some case matched=true seen=7 (expected true 7)
```

Both directions are correct: `if val` does not fire on a nil `Option`, and it
does fire — with the payload bound — on a `Some`. The positive control matters
here: without it, a binary that had regressed to "never take the `if val`
branch" would have produced a green first line and looked fixed.

Scope, and a correction to this record's own header: the body of this record
diagnoses the **Rust seed's** tree-walking interpreter fallback (its
"Suggested fix direction" section is explicitly not investigated further), so
the "SOURCE FIXED (2026-07-15)" header and the "pending a runnable pure-Simple
compiler artifact" clause do not describe the same engine the Symptom section
measured. This re-reproduction covers the seed's interpreter. The pure-Simple
interpreter's own `if val` desugar was NOT exercised — driving it from a spec
needs the parser's `if val` lowering shape, which was not reconstructed in this
pass.
