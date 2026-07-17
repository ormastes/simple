# BUG: cross-module `mut`-param class-field mutation is lost inside `std.spec` `it` blocks (not "cross-module" per se — the SSpec harness itself is the trigger)

- **Date:** 2026-07-17
- **Status:** open (root-cause narrowed; not fixed)
- **Area:** SSpec test harness (`src/lib/nogc_sync_mut/spec.spl`) interaction with the seed interpreter's closure/`mut`-param lowering
- **Severity:** medium (breaks a whole category of regression spec: any spec that wants to assert a cross-module free-fn mutated a class-typed argument)
- **Discovered while:** writing regression specs for
  `doc/08_tracking/bug/browser_script_crossmodule_mutation_breaks_timer_event_2026-07-11.md`
  (T3 lane, SSpec regression-spec sweep, 2026-07-17)

## Summary

`browser_script_crossmodule_mutation_breaks_timer_event_2026-07-11.md` frames
the observed failure as: "cross-module class-arg mutation is lost under the
seed interpreter... regardless of `mut`." That framing is **incomplete and
partially wrong**. Isolated repro below shows cross-module `mut`-param class
mutation actually **works fine** from a plain standalone `fn main()` script —
including for `EventLoop`/`timer_api.set_timeout`, the exact function the
2026-07-11 doc says is still broken. The real trigger is narrower and
different: the mutation is lost specifically when the mutating call happens
**inside a `std.spec` `it` block** (i.e. inside the actual SSpec test
harness), regardless of module boundary.

This matters because it means: **no SSpec regression spec can currently gate
"does function X's mutation of a cross-module class argument persist"**, for
ANY of the six files touched by commit 335e2d2284f (`dom_accessors.spl`,
`timer_api.spl`, `event_api.spl`, `worker_api.spl`, `clipboard_api.spl`,
`location_api.spl`) — even though standalone-script use of the exact same
functions works correctly today.

## Repro (standalone script — WORKS, no bug)

```simple
use std.gc_async_mut.gpu.browser_engine.script.event_loop.{EventLoop}
use std.gc_async_mut.gpu.browser_engine.script.timer_api.{set_timeout}

fn main() -> i32:
    val loop_ref = EventLoop.new()
    val tid = set_timeout(loop_ref, 100, 1000)
    print("tid={tid} pending={loop_ref.pending_timer_count()}")
    0
```
Output: `tid=1 pending=1` — correct, no crash, mutation persists.

The same result holds for `dom_accessors.be_dom_set_attr`/`be_dom_add_child`,
`clipboard_api.clipboard_write_text` (including a second overwrite), and
`worker_api.worker_post_message` (`.push()` accumulation) called directly
from a standalone `fn main()`.

## Repro (inside `std.spec` `it` — FAILS)

The *exact same* standalone-working functions fail when called from inside a
real `describe`/`it` block (the only way any `.spl` spec in this repo is
written):

```simple
use std.spec.{describe, it, expect}
use std.gc_async_mut.gpu.browser_engine.script.clipboard_api.{BrowserClipboard, clipboard_write_text, clipboard_read_text}

describe "probe":
    it "clipboard write persists":
        val clip = BrowserClipboard.new()
        clipboard_write_text(clip, "hello")
        expect(clipboard_read_text(clip)).to_equal("hello")   # FAILS: expected "" to equal "hello"
```
Result: `expected  to equal hello` — the write is lost even though `clip` is
constructed and mutated within the SAME `it` block (not captured from an
outer scope, not read from a different `it`). This reproduces identically for
`dom_accessors.be_dom_set_attr` and `worker_api.worker_post_message`, and
matches (with the same failure shape) the pre-existing, currently-red
`timer_api_spec.spl` (`test/01_unit/browser/script/timer_api_spec.spl`,
8 failures) and `event_api_spec.spl` (2 failures) that the 2026-07-11 doc
already tracks.

## Narrowing attempt — not purely about colon-block trailing-lambda syntax

A custom two-hop function-value pass-through using an explicit backslash
lambda (`fn run_it(body: fn()): body()`, called as `run_it(\: ...)`) does
**not** reproduce the bug at any hop depth. A custom function using the same
colon-block trailing-call syntax as `describe`/`it`
(`fn my_it(name: text, block: fn()): block()`, called as
`my_it "name": clipboard_write_text(clip, "hello") ...`) **does** reproduce a
loss (in one variant, a `field access on nil receiver` crash) when the
mutated object is captured from an *enclosing* scope — but does **not**
reproduce when the object is constructed *inside* the colon-block. The real
`std.spec.it`/`_execute_it` (`src/lib/nogc_sync_mut/spec.spl:82-115`) still
loses the mutation even with the object constructed inside the block, so the
colon-block syntax alone is not a complete explanation — `_execute_it`'s own
extra plumbing (the `for hook in before_hooks: hook()` loop and/or the
`current_test_error = nil` module-var write that run between entry and
`block()`) is implicated but not pinned down further. Not chased past this
point (diminishing returns for a stdlib-only investigation); flagged here so
whoever picks up the general interpreter/mut-param landmine has concrete
narrowing to start from instead of re-deriving it.

## Impact

- `browser_script_crossmodule_mutation_breaks_timer_event_2026-07-11.md`'s
  "Verification caveat" section should be read as: the failure is real, but
  its cause is mischaracterized (blamed on cross-module-ness, which is not
  the trigger); this doc supersedes that framing with the SSpec-`it`-block
  narrowing above. That doc's `mut` adoption itself remains correct and
  necessary (matches the landed self-hosted compiler contract) — this is not
  a request to revert it.
- Any NEW regression spec written to assert "mutation of a cross-module
  class-typed argument is visible to the caller" for `dom_accessors.spl`,
  `timer_api.spl`, `event_api.spl`, `worker_api.spl`, `clipboard_api.spl`, or
  `location_api.spl` will fail today if written as a normal SSpec `it` block
  — this is expected, not a spec bug. (Confirmed empirically for
  `dom_accessors`, `clipboard_api`, and `worker_api` in addition to the
  already-tracked `timer_api`/`event_api`.)

## Expected

`it` blocks should observe the same mutation semantics as a plain top-level
`fn main()` for cross-module `mut`-param class arguments. Until this is
fixed, SSpec cannot regression-gate commit 335e2d2284f's mutation-visibility
claim; only a standalone-script harness (matching the pattern used in
`doc/08_tracking/bug/std_process_run_standalone_crash_2026-07-17.md`'s
regression spec) can currently gate mutation-visibility functions that are
called through the `it`-block indirection.
