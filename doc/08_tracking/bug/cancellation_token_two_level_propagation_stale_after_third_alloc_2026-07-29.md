# Bug: CancellationToken depth-2 cancel propagation reads stale registry after a 3rd allocation

- **Date:** 2026-07-29 (root-caused further, same date, lane G9b)
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
  observing intervening instance-method mutations; worse across `it`/closure
  boundaries), workaround attempted and rejected (traded wrong-answer for a
  hang), see the 2026-07-29 update section below
- **Severity:** HIGH — cooperative cancellation across more than one level of
  `child()` nesting cannot be relied on yet
- **Found by:** lane G9 (mission-critical robustness campaign — cancellation semantics)
- **Related:** `doc/08_tracking/bug/interpreter_module_array_stale_read_via_free_fn_helper_2026-07-29.md`
  (a different, already-worked-around defect in the same file; this one survives that
  workaround)

## Symptom

After fixing `CancellationToken.is_cancelled()` to read the registry inline (see the
related bug above), direct parent → child cancellation is correct and covered by
`test/01_unit/lib/nogc_async_mut/cancellation_spec.spl`. But a **grandparent** case —
3 tokens, 2 levels of nesting — is not:

```
use std.async.cancellation.{token_new}

var root = token_new()
var mid = root.child()
var leaf = mid.child()
root.cancel()
mid.is_cancelled()    # returns false — should be true
leaf.is_cancelled()   # returns false — should be true
```

Reduced further: it is not about depth or `child()` specifically. Any 3rd token
allocated after `mid`, **even one wholly unrelated to `mid`**, is enough to make a
*later* recursive `mid.is_cancelled()` call go stale:

```
var root = token_new()
var mid = root.child()
val unrelated = token_new()   # <-- unrelated to mid or root
root.cancel()
mid.is_cancelled()            # still returns false
```

Whereas the 2-token case (no 3rd allocation at all between `mid`'s construction and
the check) is correct:

```
var parent = token_new()
var child = parent.child()
parent.cancel()
child.is_cancelled()          # true — correct, covered by cancellation_spec.spl
```

And a **direct** (non-recursive, base-case) read of an older token after a later
allocation is *not* affected — `parent.is_cancelled()` (which has no parent, so
returns without recursing) is correct even after `child()` allocated a new slot. Only
the *recursive* (non-base-case) path breaks, and only for a token that is not the
most-recently-touched one.

## Scope

- Verified against the current fixed `src/lib/nogc_async_mut/async/cancellation.spl`
  (post the free-fn-helper workaround), under both `bin/simple run` and
  `bin/simple test`.
- Not reproduced with exactly 2 total token allocations (root/parent + one child) —
  that case is the one covered green in `cancellation_spec.spl`.
- Reproduced with exactly 3 total allocations where the 3rd happens *after* the token
  being queried (`mid`) was constructed, regardless of whether the 3rd token is
  related to `mid`.

## Impact on this lane's deliverable

`CancellationToken` is safe to use today for the common single-scope pattern (one
token per task/operation, checked directly, at most one level of `child()` fan-out
checked immediately). It is **not** yet safe for deeper cancellation scopes (nested
sub-scopes checking an ancestor's cancellation after siblings/cousins have been
allocated) — which is exactly the "structured scopes cancel+drain children" property
called out in
`doc/01_research/language/simple_vs_rust_safety_property_audit_2026-07-28.md` line 61.
That property remains unimplemented/unverified pending this fix.

## Suggested next step

Instrument the registry reads (`_registry_cancelled[id]`, `_registry_parent[id]`)
inside the recursive branch of `is_cancelled()` to print the array's observed
length/identity at each recursion depth, comparing a 2-allocation run (passes) against
a 3-allocation run (fails), to determine whether the recursive call is binding to an
array snapshot captured at a stale point rather than the current module value. This
is an interpreter environment/binding bug, not something fixable from the `.spl`
source; out of scope for the pure-Simple-only mandate of the G9 lane that found it.

## 2026-07-29 update (lane G9b): root cause found, NOT recursion depth

Instrumented with `print()` probes against isolated scratch scripts (both plain
`bin/simple run SIMPLE_EXECUTION_MODE=interpreter` scripts and multi-`it`
`bin/simple test` spec files), replacing `is_cancelled()`'s method-to-method
recursion with a fully iterative inline `while` loop (one call frame, one method
body, re-reading `_registry_cancelled`/`_registry_parent` fresh every
iteration — no recursion, no free-fn hop at all). Result: the iterative loop
alone did **not** fix the repro. Print-instrumenting the loop showed the walk
correctly executed one iteration (self, e.g. `mid`, correctly read `false`) and
then exited — because `_registry_parent[mid.token_id]` itself had reverted to
`-1` (the placeholder `_alloc_token_id()` pushed before `child()`'s follow-up
subscript write `_registry_parent[cid] = self.token_id` ran). So it was never
about recursion; it was that the OLD allocator pushed a **placeholder** value
and overwrote it with a **separate subscript-assignment** afterward, and that
subscript write is only durable until the array's **next** `arr =
arr.push(x)` reassignment **from any call site** — a later push silently
reverts to a stale base copy that predates the write, discarding it.

Fixing that (pushing the final, correct value directly, no placeholder/overwrite
split) did not fully fix it either. Further isolation found the actual root
cause is **one level up**: a plain top-level `fn` (or `static fn`, i.e. any
callable with no `self` receiver) that mutates a module-level `var`/array is
only internally consistent **across repeated calls to that exact same
function** — it does *not* observe mutations made in between by an *instance*
method call. Minimal repro (bare `i64` counter, no array involved):

```
var root = token_new()      # free/static path, mints id 0
var mid = root.child()      # instance method, mints id 1 — correctly sees root's write
val unrelated = token_new() # free/static path AGAIN — should mint id 2...
# ...but reads _next_token_id from ITS OWN stale cross-call snapshot (still 1,
# as token_new() itself last left it) and mints id 1 again, COLLIDING with mid.
```

This reproduces identically calling `CancellationToken.new()` (a `static fn`,
no free-function indirection at all) a second time — so the defect is not
free-fn-vs-method (the OTHER bug doc's finding); it is specifically about
calling the **same receiver-less function more than once**. Calling `.child()`
repeatedly **on a `self`-bearing instance** — even the identical instance,
reused as the receiver every time — was verified correct at depth-2, depth-3,
and through 200+ sequential allocations, in a single flat script.

**Workaround attempted and REJECTED:** route every root-token allocation
through `.child()` on a lazily-created, hidden, never-cancelled "dummy"
instance (guarded by `if _root_dummy_id < 0`), so the receiver-less
`static fn new()` only ever does its own direct registry push exactly once,
ever; every subsequent root (including the very first) goes through the
proven-safe `self`-bearing `.child()` path. This fixed every case tried in a
**single flat script** (`bin/simple run SIMPLE_EXECUTION_MODE=interpreter`):
depth-2 with an intervening allocation, depth-3 with an intervening allocation
at every level, cancel-before-a-later-push, and 200+ sequential allocations —
all passed.

However, run through this file's actual `describe`/`it` spec structure
(`bin/simple test`, separate `it` blocks = separate call frames/closures), the
same workaround **corrupted state differently and non-deterministically**:
a second `it` block reusing the module state left by a prior `it` picked up a
**stale, partial** snapshot of `_next_token_id`/the registries — not fully
reset (ruling out per-`it` isolation) and not fully live either (ruling out
plain shared state) — that reused an already-assigned id, splicing a NEW
token's parent pointer onto an OLD token's leftover registry slot from a
different `it`'s scenario. Depending on exact call shape this manifested as
either a wrong-answer (`parent.is_cancelled()` spuriously `true`, borrowing an
already-cancelled ancestor from a previous unrelated `it`) or — with the
guard variant that unconditionally pushed a fresh dummy on every call — a
`test daemon timed out` hang (consistent with a corrupted/cyclic parent chain
making the iterative loop spin forever; see the companion interpreter bug doc
for the exact probe transcripts).

**Decision:** per this lane's escalation rule, the workaround was **not**
shipped — trading a deterministic wrong-answer for a hang is a regression, not
a fix. What shipped instead in
`src/lib/nogc_async_mut/async/cancellation.spl`: (1) the placeholder-then-
overwrite allocation pattern was removed (every push writes its final,
correct value directly); (2) `is_cancelled()` is a bounded iterative loop
(capped at `registry length + 1` steps, failing toward `true`/cancelled if the
bound is hit) so a future corrupted/cyclic parent chain can never hang the
process, only give a conservative answer. This keeps the direct parent/child
case (depth-1, one `token_new()` call per `it`) correct and covered by
`cancellation_spec.spl` (8/8 green), plus the two other regression suites
(`async_spec.spl` 10/10, `async_host_spec.spl` 7/7). Depth-2+ propagation
across more than one `token_new()`/`.new()` call remains **open and
unasserted** in the spec — this is a genuine, unresolved interpreter defect
(receiver-less function calls not observing intervening instance-method
mutations, worse across separate `it`/closure frames than within one), not
expressible or fixable from pure-Simple stdlib source. Recommended next step
for the interpreter/compiler team: bisect why a `static fn`/free `fn`'s
resolution of a module-level `var` differs from an instance method's, and
why crossing a `describe`/`it` closure boundary makes it worse (partial, not
full, state reset) rather than the same as crossing a plain function-call
boundary within one script.
