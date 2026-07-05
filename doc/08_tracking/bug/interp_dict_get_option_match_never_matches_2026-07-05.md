---
id: interp_dict_get_option_match_never_matches_2026-07-05
status: OPEN
severity: medium
discovered: 2026-07-05
discovered_by: std.diag (easy-debug-infra P0) implementation + spec work
related: src/lib/nogc_sync_mut/diag.spl
related: test/01_unit/lib/nogc_sync_mut/diag_spec.spl
---

# `if val Some(x) = dict.get(k):` silently never matches

## Summary

`Dict<K,V>.get(k)` returns the raw value or `nil` — it does NOT return a
`Some(..)`-tagged `Option<V>`. Code that pattern-matches the result as an
Option therefore silently takes the `else`/no-match branch every time, with
no error or warning:

```simple
# BUG: this branch is NEVER taken, even when k is present in d
if val Some(x) = d.get(k):
    use(x)
else:
    fallback()
```

Workaround, both proven correct in `diag.spl`:

```simple
val x = d.get(k) ?? default_value
# or
val v = d.get(k)
if v != nil:
    use(v)
```

## Evidence

Found while implementing `src/lib/nogc_sync_mut/diag.spl` (module docstring
lines 33-37 record the landmine directly). Affected call sites in that module
use the `?? default` / `!= nil` form throughout, e.g. `_g_stage_last_ms.get(
component) ?? now` (stage delta), `_g_deadline_armed_at.get(label)` checked
via `!= nil`, `_g_timer_stats.get(label)` checked via `== nil`/`!= nil`.

## Impact

Any code written against the natural assumption that `Dict.get` returns an
`Option` (consistent with `Some(x)`/`None` pattern-matching used elsewhere in
the language) silently no-ops instead of erroring — a correctness footgun
that produced zero test failures until manually traced. Affects every module
using `Dict<K,V>` with `if val Some(x) = ...:` on a `.get()` result.

## Scope

Interpreter semantics of `Dict.get()` return type vs the `if val Some(x) = `
pattern-match sugar; not specific to `std.diag`.
