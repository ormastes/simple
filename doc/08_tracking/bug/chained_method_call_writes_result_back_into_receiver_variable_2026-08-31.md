# Chained method call writes its result back into the receiver variable (interpreter)

**Date:** 2026-08-31
**Status:** OPEN
**Severity:** High — silently corrupts an immutable `val` binding
**Layer:** Rust seed interpreter (`src/compiler_rust/compiler/src/interpreter*`)
**Found while fixing:** C14 (`src/lib/nogc_sync_mut/src/table.spl`), spec
`test/feature/usage/table_spec.spl` example "supports multiple aggregations".

## Symptom

A two-link method chain `t.f(...).g(...)` assigns the FINAL result back into
the root variable `t`, even when `t` is a `val`. Neither `f` nor `g` is a `me`
method and neither mutates anything.

The equivalent split form is correct, which is what makes this a chaining bug
rather than an aliasing bug in the callee:

```
val t = <Table with 3 rows>
val h = t.head(2).head(1)     # t is now the 1-row table
print(t.nrows())              # 1   -- WRONG, expected 3

val u = <Table with 3 rows>
val u1 = u.head(2)
val u2 = u1.head(1)
print(u.nrows())              # 3   -- correct
```

## Reproduction

`bin/simple run` on:

```
use std.src.table.{Table, Column}
fn mkt() -> Table:
    var d = {}
    d["x"] = ["A", "B", "C"]
    d["y"] = [5, 10, 15]
    Table.from_dict(d)
fn main():
    val t = mkt()
    val h = t.head(2).head(1)
    print("HEADCHAIN t nrows={t.nrows()} h={h.nrows()}")   # t nrows=1  (bug)
    val u = mkt()
    val u1 = u.head(2)
    val u2 = u1.head(1)
    print("HEADSPLIT u nrows={u.nrows()}")                 # u nrows=3  (ok)
```

Observed on the Rust seed at `origin/main` 5f8458fefd8.

## How it breaks table_spec

`table1.group_by(["x"]).agg({"y": "sum"})` overwrites `table1` with the
aggregated result. A second `table1.group_by(["x"]).agg({"y": "mean"})` then
looks up column `"y"` in a table that only has `x` / `y_sum`, gets `nil`, and
fails with ``method `get` not found on type `nil` ``. This is why the spec's
first two group_by examples pass (one aggregation each, distinct tables) and
only the "supports multiple aggregations" example fails.

## Ruled out (each tested by editing table.spl and re-running the repro)

- Method-name collision between `Table.agg` and `GroupedTable.agg` — renaming
  `Table.agg` changes nothing.
- `Table.__getattr__` — disabling it changes nothing.
- `GroupedTable` holding `table: self` — replacing it with an explicit
  field-by-field `Table(...)` copy changes nothing.
- Not reproducible with small same-file `struct`s (Box/Holder, with and without
  a `Dict` field and a `me` method), so it needs the real Table shape and/or a
  cross-module import.

## Fix scope

Interpreter, not stdlib. No pure-Simple change to `table.spl` can avoid it
without removing the chained call from the SPEC, which is not allowed.

## Related, found in the same session

`d[k].push(v)` on a `Dict<text, [Any]>` field inside a method silently does NOT
mutate the stored array (it produced empty aggregation columns), while the same
form on a `Dict<text, [i64]>` local at top level DOES mutate. `table.spl`
therefore keeps `d[k] = d[k].push(v)` at four dict-slot sites; the array-local
COW-alias sites were all converted to in-place `xs.push(v)`.
