# dbfs_checkpoint_attr_facade specs still red: `self` not found + missing gc tier module

- **Status:** FIXED 2026-06-11
- **Found:** 2026-06-11, exposed by the `gen` → `slot_gen` rename (see
  `dbfs_checkpoint_gen_reserved_keyword_2026-06-11.md`); previously MASKED
  because the spec failed earlier at the reserved-keyword parse error.
- **Severity:** medium — both tier copies of the facade spec fail in
  interpreter mode; the modules they exercise are covered indirectly by the
  green integration specs (dbfs_engine_checkpoint 6/6, checkpoint_ring 8/8,
  ring_diag 6/6), so this is a facade/spec-path gap, not a data-integrity gap.

## Symptoms

1. `test/01_unit/lib/nogc_async_mut/db/dbfs_engine/dbfs_checkpoint_attr_facade_spec.spl`
   fails: `semantic: variable 'self' not found`. The spec itself contains no
   `self`; the error comes from library code reached through the
   `std.nogc_async_mut.db.dbfs_engine` facade import path — likely the known
   interpreter strictness around `self`/`me` receivers when methods are
   re-exported across module facades.
2. `test/01_unit/lib/gc_async_mut/db/dbfs_engine/dbfs_checkpoint_attr_facade_spec.spl`
   fails: `Cannot resolve module: std.gc_async_mut.db.dbfs_engine` — the
   gc_async_mut tier has no `db/dbfs_engine` wrapper module at all
   (`src/lib/gc_async_mut/db/dbfs_engine/` does not exist).

## Root cause (verified 2026-06-11)

**Defect 1 — `self` not found in interpreter:**

The interpreter requires `me fn` / `me.` for all mutable methods. Several
methods in the dbfs_engine stack were declared as plain `fn` with `self.`
field access. In interpreter mode (the fallback path when HIR lowering
fails, e.g. for generic BTree operations), these fail at runtime with
`semantic: variable 'self' not found`.

There is also a distinct Rust interpreter bug: passing `me.field` DIRECTLY
as an argument to a nested `me fn` call also triggers `self not found`. For
example:

```
# Fails:
me fn query(q: AttrQuery) -> AttrQueryResult:
    ids = me._query_index(me.size_index, q.op)  # me.size_index as direct arg

# Works:
me fn query(q: AttrQuery) -> AttrQueryResult:
    var idx_copy = me.size_index
    ids = me._query_index(idx_copy, q.op)  # copy to local first
```

This is a seed (Rust interpreter) bug. Workaround: always copy `me.field`
to a local `var` before passing to a nested `me fn` call.

Affected files converted from plain `fn self.` to `me fn me.`:
- `src/lib/nogc_sync_mut/storage/shared/btree.spl`
- `src/lib/nogc_sync_mut/storage/shared/checkpoint_ring.spl`
- `src/lib/nogc_sync_mut/db/dbfs_engine/ns_btree.spl`
- `src/lib/nogc_async_mut/db/dbfs_engine/ns_btree.spl`
- `src/lib/nogc_sync_mut/db/dbfs_engine/pager.spl`
- `src/lib/nogc_sync_mut/db/dbfs_engine/checkpoint.spl`
- `src/lib/nogc_sync_mut/db/dbfs_engine/attr_index.spl` (also applied local-copy workaround in `query` and `_remove_from_field_index`)
- `src/lib/nogc_sync_mut/db/dbfs_engine/schema.spl`

**Defect 2 — missing gc_async_mut tier module:**

`src/lib/gc_async_mut/db/` and `src/lib/gc_async_mut/db/dbfs_engine/` did
not exist. Created `__init__.spl` export-use wrappers following the
established tier-wrapper pattern (no `std.` prefix):

```
# src/lib/gc_async_mut/db/__init__.spl
export use nogc_async_mut.db.*

# src/lib/gc_async_mut/db/dbfs_engine/__init__.spl
export use nogc_async_mut.db.dbfs_engine.*
```

## Verification (2026-06-11)

All four specs pass (interpreter mode, timeout 240s):

| Spec | Result |
|------|--------|
| `test/01_unit/lib/nogc_async_mut/db/dbfs_engine/dbfs_checkpoint_attr_facade_spec.spl` | PASSED (1076ms) |
| `test/01_unit/lib/gc_async_mut/db/dbfs_engine/dbfs_checkpoint_attr_facade_spec.spl` | PASSED (1119ms) |
| `test/02_integration/storage/dbfs/dbfs_engine_checkpoint_spec.spl` | PASSED (6 examples, cached) |
| `test/02_integration/storage/dbfs/dbfs_engine_checkpoint_ring_spec.spl` | PASSED (8 examples, cached) |

## Open Rust seed bug

The `me.field as direct arg to me fn` interpreter failure is a seed bug.
Minimal repro is in the root-cause section above. Not fixed in Rust — the
local-copy workaround is sufficient for all current call sites. File a
separate bug if new code hits it.
