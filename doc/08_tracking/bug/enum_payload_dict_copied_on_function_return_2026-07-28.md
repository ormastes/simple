# Enum collection payload is copied at the function-return boundary

- **Date:** 2026-07-28
- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Severity:** high — silently wrong results, no diagnostic
- **Engines:** interpreter (silently wrong) and JIT (rejects with W1006)
- **Found via:** `SdnValue.insert()` never persisting (`test/01_unit/lib/common/sdn_coverage_spec.spl`, example "get by key from dict")

## Summary

An enum variant holding a `Dict<K, V>` payload keeps a live alias to that dict
**only while the enum value stays inside the frame that constructed it**. As
soon as the enum is returned from a function, the payload is copied: any write
made through a handle obtained from a later `match` lands on a dead copy, and
subsequent reads see the pre-write state. There is no error and no warning.

## Reproduction

`build/smallfix_probe3.spl` (four variants of the same code):

| # | how the enum was built | write persists? |
|---|------------------------|-----------------|
| L | `var m: Dict<text,i64> = {}` then `Box.Dict(m)` **in the caller's frame** | YES (reads back 7) |
| K | `Box.empty()` — static ctor returning `Box.Dict({})` | NO (reads back -1) |
| M | `Box.empty()` + inline `match` in the caller (no method) | NO |
| N | `Box.empty_named()` — static ctor that names the dict local first | NO |

So the copy is caused by the **return boundary**, not by the dict literal, not
by the method call, and not by the `match`.

Two adjacent facts that are NOT the cause (each verified separately):

- Dicts are reference-semantic through a `mut` parameter
  (`build/smallfix_probe2.spl`, case G reads back 7).
- An enum payload aliases the dict it was constructed from — mutating the
  original local after construction is visible through the enum
  (`build/smallfix_probe2.spl`, case I reads back 7), and mutating the `match`
  binding via a `mut`-param helper is visible too (case J reads back 7).

## Secondary defect: immutable match binding drops the write silently

`case Dict(d): d[key] = value` inside the match is a no-op on the interpreter.
The JIT is correct here and refuses it:

```
HIR lowering error: Memory safety error [W1006]: mutation without mut capability
```

The interpreter should raise the same error instead of discarding the write.

## Also does not work

- `fn insert(mut self, ...)` reassigning `self = Enum.Dict(copy)` — the new
  `self` is not visible to the caller (`build/smallfix_probe.spl`, case B).
- Boxing the dict in a class and putting the class in the payload — a class
  payload behaves the same way (`build/smallfix_probe4.spl`, case O reads back
  -1, and `c.m[k] = v` needs `mut c`).

## Impact

`SdnValue.insert()` / `SdnValue.push()` cannot offer mutating semantics for any
value obtained from a constructor. `SdnValue.empty_dict()` → `.insert(k, v)` →
`.get(k)` returns nil. `src/lib/common/sdn/value.spl` carries a comment
pointing at this file; the affected spec example is left RED on purpose rather
than rewritten to dodge the defect.

## Suggested fix

Stop deep-copying collection payloads when an enum value crosses a return
boundary (keep the handle), or make the copy explicit and consistent so that
in-frame mutation does not appear to work. Either way, the interpreter must
stop silently discarding a write through an immutable `case` binding.
