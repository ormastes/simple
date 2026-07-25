# Bug: member-path stores silently lost inside BDD it-block closures

**Date:** 2026-07-03
**Severity:** Medium-High — silently no-ops writes, producing false test
failures (or worse, false passes) for any spec that mutates object state
directly inside an `it` block.
**Component:** interpreter closure/lvalue execution (self-hosted binary
`bin/release/x86_64-unknown-linux-gnu/simple`; same family as
`interp_crossmodule_array_writeback_lost_in_bdd_closure_2026-06-29.md` and
`interp_enum_arg_corruption_in_bdd_closure_2026-06-30.md`).
**Status:** Source fixed; execution verification pending.
**Found by:** rollball production spec lane (W6d event-handling gap check).

## Symptom

Inside a BDD `it`-block closure, any store through a member path deeper than
one plain scalar field mutates a **copy** and is silently lost. The same
statements in a top-level `fn` (called from the same `it` block) work.

| store shape (inside `it`)       | result   |
|---------------------------------|----------|
| `o.n = 5` (1-level scalar)      | works    |
| `o.vals[i] = v` (member array)  | LOST     |
| `o.inner.n = v` (2-level scalar)| LOST     |
| `o.inner.vals[i] = v`           | LOST     |

## Minimal reproducer

```simple
use std.spec.*

class Flat:
    vals: [f64]
    n: i64

describe "store shapes inside it":
    it "one-level member array store":
        var o = Flat(vals: [1.0, 2.0], n: 0)
        o.vals[0] = 50.0
        assert_equal(o.vals[0], 50.0)   # FAILS: reads back 1.0
```

Run: `bin/release/simple run repro_spec.spl` (also fails under
`bin/simple test`). Moving the two mutation lines into a top-level `fn` and
calling it from the `it` block passes.

## Impact seen

`test/03_system/game3d/rollball_production_spec.spl` event/animation scenarios
originally wrote `world.bodies.vel_x[bi] = ...` inside `it` blocks; the input
was silently dropped, so the ball never moved (x stayed -9.0 after 1200 driven
steps) while `world.step()` (mutation inside methods) kept working. The spec
now routes all direct body writes through top-level session helpers
(`run_scripted`, `run_win_then_terminal_input`, `win_snapshots`) — which is
also how the game itself (`src/app/game.rollball/game.spl`) is structured, so
the shipping game is not affected.

## Fix direction

The `it` body executes as a closure; its lvalue resolution for member-path
stores appears to operate on a dereferenced copy of the closure-local binding
instead of the underlying object handle. Fix in the interpreter's compound
assignment/store path for closure frames so `obj.field[i]` / `obj.a.b`
resolve the same object identity as in plain function frames. Add the four
store shapes above as an interpreter regression spec.

## Resolution (2026-07-15)

The closure executors had two partial copies of plain-assignment dispatch that
only handled field and index receivers when the receiver was a direct
identifier. Both closure paths now delegate to the interpreter's canonical
`exec_assignment`, which already owns nested field and member-index writeback.
The clone-isolated BDD path retains its existing module-global write-through
policy after shared assignment dispatch.
The interpreter field-assignment spec covers all four store shapes directly
inside `it` closures. Execution remains pending an authorized runtime test run.
