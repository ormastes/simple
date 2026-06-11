# dbfs checkpoint structs use reserved keyword `gen` as field name

- **Status:** open
- **Found:** 2026-06-11 (during E5 pager WAL gate verification)
- **Severity:** medium — `dbfs_checkpoint_attr_facade_spec.spl` (both gc_async_mut
  and nogc_async_mut copies) fails in interpreter mode; not introduced by E5
  (confirmed identical `gen` usage at remote tip before the E5 change).

## Symptom

`bin/simple test test/01_unit/lib/nogc_async_mut/db/dbfs_engine/dbfs_checkpoint_attr_facade_spec.spl`
fails: `CheckpointEngine.reopen` declares `val gen = match latest: ...` and the
checkpoint structs declare `gen: i64` fields. `gen` is a reserved keyword in
the interpreter/parser, so execution breaks at these sites.

## Affected sites

- `src/lib/nogc_sync_mut/db/dbfs_engine/checkpoint.spl` — struct fields at
  lines ~15, ~80, ~84; `val gen` + constructor args at ~35–66, ~118, ~149
- `src/lib/nogc_async_mut/db/dbfs_engine/checkpoint.spl` — parallel tier copy
- `src/lib/nogc_sync_mut/db/dbfs_engine/checkpoint_ring.spl`, `recovery.spl`,
  `meta_store.spl`, `fs_driver.spl` — consumers of the structs
- `test/01_unit/lib/{gc_async_mut,nogc_async_mut}/db/dbfs_engine/dbfs_checkpoint_attr_facade_spec.spl`
  — external `.gen` field accesses (`ring.current_slot().unwrap().gen`)

## Fix direction

Rename the field/local to a non-reserved name (e.g. `ckpt_gen` or `slot_gen`)
across both tier copies and all consumers + specs in one commit. Alternatively
un-reserve `gen` in field/member position in the parser, which would also fix
other libraries hitting the same cliff — prefer whichever matches parser-team
direction. Do NOT skip or weaken the facade specs.
