# `Map.new()` resolves to a plain `dict` (not the `Map<K,V>` struct); `insert_if_absent` missing either way

**Date:** 2026-07-20
**Found by:** whole-suite `test/unit/` triage campaign,
`test/unit/lib/nogc_async_mut/src/map_insert_if_absent_spec.spl`
**Status:** open — genuine defect/missing-feature, not a stale test

## Symptom

```
semantic: method `insert_if_absent` not found on type `dict` (receiver value: {})
```

```simple
use std.nogc_async_mut.src.map.{Map}

var map: Map<text, i32> = Map.new()
expect(map.insert_if_absent("name", 1)).to_equal(true)
```

Two layered issues:

1. **`Map.new()` produces a value the interpreter reports as type `dict`**
   (receiver printed as `{}`), not as the `Map<K, V>` struct declared in
   `src/lib/nogc_sync_mut/src/map.spl:20` (`struct Map<K, V> where K: Hash +
   Eq: buckets: [...], size: i32, capacity: i32`, `static fn new()`). This
   matches the project's known "same struct/constructor name collision
   across modules" interpreter landmine (see memory:
   `feedback_interp_struct_name_collision_global_registry` and the
   recurring "`Map.new()` #185" clobber signature referenced in campaign
   history) — something elsewhere in the resolved module graph is shadowing
   `Map.new` with a builtin empty-dict-returning path.
2. **`insert_if_absent` is not implemented on the `Map<K,V>` struct at all**
   — grepping `src/lib/nogc_sync_mut/src/map.spl` (the backing definition;
   `nogc_async_mut/src/map.spl` and `gc_*` tiers just re-export it) finds no
   `fn insert_if_absent`. Even if issue (1) were fixed and the receiver were
   a genuine `Map` struct instance, this method would still be missing —
   this is a real API gap, not a resolution artifact.

## Affected spec

- `test/unit/lib/nogc_async_mut/src/map_insert_if_absent_spec.spl` — single
  `it` block, fails at the first `insert_if_absent` call.

## Why this isn't a stale-test fix

There is no current, differently-named method that provides
insert-if-absent semantics on `Map<K,V>` to swap in (checked: only `new`,
`with_capacity`, and standard get/insert/remove-shaped methods are present
in `map.spl`; no `get_or_insert`/`try_insert` equivalent). Implementing
`insert_if_absent` is a real feature addition to
`src/lib/nogc_sync_mut/src/map.spl`, out of scope for a test-triage pass
(src/** edits restricted to unambiguous one-line renames per the fix-guide).

## Scope note

Root cause of issue (1) — why `Map.new()` yields a `dict`-typed receiver
instead of a `Map` struct instance — not traced further this pass (would
require walking the full import graph reached from
`std.nogc_async_mut.src.map` to find the colliding declaration). Flagged as
the likely primary blocker since it means even a correctly-implemented
`insert_if_absent` on the `Map` struct would not be reachable through this
import path until the collision is resolved.
