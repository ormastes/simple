# Bug: instance method reads a stale module-level array through a free-function helper (interpreter)

- **Date:** 2026-07-29
- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  cause is in the interpreter, not fixable from pure Simple stdlib code)
- **Severity:** CRITICAL — silently wrong results, no error, on the default test engine
- **Found by:** lane G9 (mission-critical robustness campaign — cancellation semantics audit)

## Symptom

`src/lib/nogc_async_mut/async/cancellation.spl`'s `CancellationToken` is the **only**
real cancellation-token implementation in the codebase (the audit doc
`doc/01_research/language/simple_vs_rust_safety_property_audit_2026-07-28.md` calls it
out at line 120 as "`CancellationToken` implemented"). Before this fix, calling
`token.cancel()` never made a subsequent `token.is_cancelled()` return `true` —
**on either engine** (`bin/simple run`'s JIT-with-interpreter-fallback, and
`bin/simple test`'s pure tree-walk interpreter). This was verified against the
unmodified file at HEAD (934328d5a6a), so it predates this session and is not a
regression from anything in this campaign:

```
use std.async.cancellation.{token_new}
var t = token_new()
t.cancel()
t.is_cancelled()   # returned false — should be true
```

No test ever caught this: `test/01_unit/lib/nogc_async_mut/async_spec.spl` defines its
**own local stub** `class CancellationToken` (different field layout, no registry, no
parent chain) instead of importing the real type, and
`test/01_unit/lib/nogc_async_mut/async_host_spec.spl` only string-matches the source
text of `async_host/handle.spl` (`src.contains("me cancel()")` etc.) rather than
constructing anything. So the real implementation had **zero** behavioral coverage.

## Root cause (minimally repro'd, isolated from this file's names)

The break is **not** specific to `CancellationToken`, module path, growable vs. fixed
arrays, or a two-array registry. It is: **a class method that reads a mutated
module-level array *through a separate top-level `fn` helper* sees a stale snapshot,
while the same read done *inline in the method body itself* sees the live value.**

Minimal repro (arbitrary names, single `[bool]` array, single class, no recursion):

```
var _flags: [bool] = []

fn alloc() -> i64:
    val id = _flags.len()
    _flags = _flags.push(false)
    id

fn _read(id: i64) -> bool:      # <-- the free-function indirection
    _flags[id]

class Thing:
    id: i64

impl Thing:
    me mark():
        _flags[self.id] = true

    fn check() -> bool:
        _read(self.id)          # <-- goes through _read: STALE (returns false)
        # _flags[self.id]       # <-- inline instead: correct (returns true)
```

Under `bin/simple test`, `t.mark(); t.check()` returns `false` with the `_read(...)`
indirection and `true` with the inline read — same array, same object, same call
site, only the presence of the free-function hop differs. Confirmed with both the
recursive form (`_token_is_cancelled_by_id`, the original shape in
`cancellation.spl`) and this non-recursive minimal form; confirmed with one array and
with two parallel arrays; confirmed under both `bin/simple run` and `bin/simple test`
(this specific repro reproduces on both — other variants during isolation reproduced
on `run` and not `test` or vice versa, so the divergence between the two engines noted
in `doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md` layers on top of
this and makes it easy to get a false negative by testing only one engine).

## Known-good workaround (used in the fix)

Do the registry read **inline inside the method that owns `self`**, and do any
recursion by constructing a **new instance** of the same class and calling the same
method on it (method-to-method), never by calling a plain top-level `fn` that reads
the array:

```
impl Thing:
    fn check() -> bool:
        if _flags[self.id]:
            true
        else:
            ...
            val other = Thing(id: some_other_id)
            other.check()          # <-- method-to-method recursion: correct
```

This is what `CancellationToken.is_cancelled()` now does
(`src/lib/nogc_async_mut/async/cancellation.spl`).

## Known remaining gap: depth-2+ propagation still stale after a 3rd allocation

Even with the workaround, a **separate** manifestation survives: if any additional
token is allocated (`token_new()` or `.child()`, related or not) *after* a given token
was constructed, a **later** recursive (non-base-case) `is_cancelled()` call on that
*earlier* token can still read a stale registry and wrongly return `false`. Direct
parent/child (exactly 2 tokens, no intervening allocation) is correct and is covered
by `test/01_unit/lib/nogc_async_mut/cancellation_spec.spl`. Depth-2 (grandparent) is
not — see
`doc/08_tracking/bug/cancellation_token_two_level_propagation_stale_after_third_alloc_2026-07-29.md`
for the isolated repro. This is filed separately because its trigger condition (an
intervening allocation, not a free-fn hop) is different from the one root-caused here
and the same reproduction technique did not converge on a single-cause explanation
within this lane's scope.

## Why this belongs to the interpreter/compiler team, not this lane

This lane (G9, mission-critical robustness campaign) is scoped to pure-Simple stdlib
changes only, no runtime/interpreter changes. The defect is in how the tree-walk
interpreter (and, per the repro, sometimes the JIT-with-fallback path too) resolves
reads of a module-level `var` array from inside a call reached indirectly through a
plain function versus directly inside the calling method — almost certainly a
variable-slot/environment-binding bug in the interpreter's call-frame handling, not
anything expressible or fixable in `.spl` source beyond the workaround above.

## Suggested next step

Bisect the interpreter's environment/frame construction for calls made from inside an
`impl` method body to a top-level `fn`, versus calls made to another method on a
freshly-constructed instance of the same class — the workaround above suggests the
latter re-resolves the module scope correctly while the former does not.

## 2026-07-29 update (lane G9b): broader than free-fn-vs-method

Chasing the "known remaining gap" above to ground, lane G9b (mission-critical
robustness campaign) found the defect is broader than "free-fn helper called
from inside a method": it reproduces for **any receiver-less callable
(a plain top-level `fn`, or a `static fn` with no `self`) called more than
once**, regardless of whether a method is involved at all. Minimal repro
(bare `i64` counter, `bin/simple run SIMPLE_EXECUTION_MODE=interpreter`):

```
var root = token_new()       # 1st call into a receiver-less fn: mints id 0
var mid = root.child()       # instance method (self-bearing): mints id 1, correctly
                              # sees the counter as token_new() left it
val unrelated = token_new()  # 2nd call into the SAME receiver-less fn: should
                              # mint id 2, but reads a stale cross-call snapshot
                              # (still 1) and mints id 1 again — collides with mid
```

Calling `CancellationToken.new()` (a `static fn`, no free-fn indirection
whatsoever) a second time reproduces the identical collision, ruling out
"free-fn helper" as the necessary condition — it is specifically about
**repeated calls to a receiver-less function**, whether or not a method calls
it or it's called directly. Calling an **instance** method (`.child()`) many
times in a row — even reusing the exact same receiver value — was verified
correct through 200+ sequential calls in one script.

A worse variant surfaces crossing a `describe`/`it` spec closure boundary
(`bin/simple test`): a later `it` block's first call into a receiver-less
function does not see a full reset (ruling out per-test isolation) nor fully
live state (ruling out ordinary shared globals) but a **stale, partial**
snapshot — enough to mint a colliding id with an unrelated earlier `it`'s
token and splice a fresh token's parent pointer onto that old slot's leftover
registry data. One workaround shape for this even produced a
`test daemon timed out` hang, consistent with the corruption occasionally
producing a cyclic parent chain.

Full transcript, working code that reproduces it in isolation, the workaround
attempted (and why it was rejected — see "Decision" there), and what shipped
instead: the 2026-07-29 update section of
`doc/08_tracking/bug/cancellation_token_two_level_propagation_stale_after_third_alloc_2026-07-29.md`.
Still not fixable from pure-Simple stdlib source; still belongs to the
interpreter/compiler team.

## Re-verification 2026-08-17 — DOES NOT REPRODUCE

Ran the doc's verbatim reproducer (module-level `var _flags: [bool]`, `alloc()`,
the `_read(id)` free-function indirection, `Thing.mark()` / `Thing.check()`) on
the deployed seed under `SIMPLE_EXECUTION_MODE=interpreter`. Both paths agree:

    via_helper=true  inline=true

This doc records `via_helper` returning the STALE `false` while the inline read
returned `true`. That divergence is gone. Very likely closed together with
`module_global_write_lost_on_frame_pop_2026-07-28.md`, whose
`sync_owned_captured_globals()` return-direction clobber is the same mechanism
seen from a different angle — a module-global write dying on frame pop is
exactly what makes a read through an extra call hop look stale.

Not proven: the "2nd call to a receiver-less fn mints a colliding id" broader
form from the 2026-07-29 update was not separately exercised.
