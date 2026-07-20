# Bug: `src/lib/nogc_sync_mut/src/table.spl` has 4 real gaps (missing `Set` import, missing array `sorted_by`, broken `group_by`/`agg`, broken `value_counts`)

- **Date:** 2026-07-20
- **Status:** open (found triaging `test/feature/usage/table_spec.spl` after
  fixing its stale `use std.table.*` import and free-function-style API calls
  to match the real `Table`/`Column` OOP API — see that spec's diff)
- **Area:** `src/lib/nogc_sync_mut/src/table.spl` (library source, no rebuild
  needed — interpreted directly), deployed seed at
  `bin/release/x86_64-unknown-linux-gnu/simple`

## Symptom

After aligning `table_spec.spl` to the real API (`Table.from_dict(...)`,
`Column.from_ints(...)`, `table.nrows()`, etc. — the file previously called
nonexistent free functions like `table_from_dict`/`column_sum`, a stale-test
issue fixed separately), 5 of 25 examples still fail on genuine library bugs:

```
✗ sorts ascending by column / sorts descending
  semantic: method `sorted_by` not found on type `array` (receiver value: [0, 1, 2])
  -- Table.sort_by() internally calls indices.sorted_by(\i, j: ...) (table.spl ~line 414);
     no `sorted_by` method exists on array under this interpreter.

✗ supports multiple aggregations
  semantic: method `get` not found on type `nil` (receiver value: nil)
  -- table1.group_by(["x"]).sum(["y"]) / .mean(["y"]) hit this internally.

✗ gets unique values
  semantic: variable `Set` not found
  -- Column.unique() (table.spl line 186) calls `Set.new()` but table.spl never
     imports Set (src/lib/nogc_sync_mut/src/set.spl defines it); it evidently
     relies on Set being available as an ambient/prelude global in whatever
     context table.spl is normally used from, which isn't true when imported
     standalone via `use std.nogc_sync_mut.src.table.*`.

✗ counts value occurrences
  expected 0 to equal 3
  -- Column.value_counts() (table.spl line 194) returns a Table; test checks
     `.nrows()`, got 0 instead of 3 (one row per distinct value) — the
     dict-based counting loop or the Table.from_columns() call it feeds
     produces an empty table.
```

## Root cause

Four independent gaps in `table.spl`, not a single root cause:

1. `Column.unique()` uses `Set` without an import — trivial one-line fix
   (`use set.{Set}` or equivalent sibling-module import), not attempted here
   to keep this pass scoped to the test cluster rather than editing shared
   library internals with unknown blast radius (other consumers:
   `gc_async_mut`/`nogc_async_mut`'s `export use ... src.table.*` re-exports).
2. `Table.sort_by()` depends on an array method (`sorted_by` with a 2-arg
   comparator closure) that doesn't exist under this interpreter — either the
   method needs adding to the array builtin surface, or `sort_by` needs
   rewriting to use whatever sort primitive IS available.
3. `GroupedTable.sum()`/`.mean()` (or the `agg()` they likely delegate to)
   produce a `nil` somewhere that a subsequent `.get(...)` call chokes on —
   not root-caused further in this pass.
4. `Column.value_counts()` produces a 0-row table instead of one row per
   distinct value — not root-caused further in this pass (could be the same
   `Dict<Any,i64>` counting loop, or the `Table.from_columns()` call at the
   end of the method).

## Fix direction (not applied — library source, but shared across 3+ tiers, deferred to whoever owns table.spl)

1. Add `use set.{Set}` (or the correct sibling-import form) to `table.spl`.
2. Either implement `sorted_by` on the array builtin, or rewrite
   `Table.sort_by()`'s index-sort to avoid it.
3. Trace `GroupedTable.sum()`/`.mean()`/`.agg()` for the `nil` source.
4. Trace `Column.value_counts()`'s counting/table-construction path.

## Verification

Reproduced at repo tip (2026-07-20) via:
```
bin/release/x86_64-unknown-linux-gnu/simple test test/feature/usage/table_spec.spl --no-session-daemon
```
20/25 examples pass after the import-path + API-alignment stale-test fix; the
5 above are the genuine remainder. Not checked against the pure-Simple
self-hosted compiler — only the Rust seed interpreter was probed, though this
particular fix (unlike the other bugs filed this pass) does not require a
rebuild since `table.spl` is regular interpreted library source.
