# Bug: CancellationToken depth-2 cancel propagation reads stale registry after a 3rd allocation

- **Date:** 2026-07-29
- **Status:** open
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
