# dbfs_checkpoint_attr_facade specs still red: `self` not found + missing gc tier module

- **Status:** open
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

## Fix direction

1. Root-cause the `self` resolution failure on the nogc_async_mut facade path
   (minimal repro: import CheckpointEngine via the facade and call a me-method).
2. Add the missing gc_async_mut export-use wrapper for db/dbfs_engine
   (pattern: nogc_async_mut is the default tier; other tiers wrap — see the
   12 export-use wrappers added 2026-06-11).
Do NOT skip or weaken either spec.
