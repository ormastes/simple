# `gc_async_mut` tier missing facade wrapper modules for several subsystems (`compression`, `database.sql`, ...)

**Date:** 2026-07-20
**Found by:** whole-suite `test/unit/` triage campaign, cluster
`test/unit/lib/gc_async_mut/**`
**Status:** open — same defect class as the already-FIXED
`dbfs_checkpoint_facade_spec_self_not_found_2026-06-11.md` "Defect 2", but a
different/newer set of subsystems; needs the same treatment (or the earlier
fix regressed — not distinguished here, see Regression note).

## Symptom

Specs under `test/unit/lib/gc_async_mut/**` import from
`std.gc_async_mut.<subsystem>.<module>` paths that resolve to nothing:

```
error: semantic: Cannot resolve module: std.gc_async_mut.compression.lz4
error: test-runner: no examples executed
```

```
error: semantic: Cannot resolve module: std.gc_async_mut.database.sql.escape
error: test-runner: no examples executed
```

`src/lib/gc_async_mut/` has no `compression/` directory at all (only an
unrelated `compress/` dir with a different, unified `compress()`/`decompress()`
API — not the lz4/zlib/gzip/brotli submodule split the spec expects) and no
`database/sql/` directory. The backing family module DOES exist at
`src/lib/nogc_async_mut/compression/{lz4,zlib,gzip,brotli}.spl` — only the
`gc_async_mut` tier's re-export wrapper is missing.

## Precedent (already fixed once, for a different subsystem)

`doc/08_tracking/bug/dbfs_checkpoint_facade_spec_self_not_found_2026-06-11.md`
hit the exact same "Cannot resolve module: std.gc_async_mut.db.dbfs_engine"
symptom for `db/dbfs_engine`, and fixed it 2026-06-11 by adding thin
export-use wrapper modules:

```simple
# src/lib/gc_async_mut/db/__init__.spl
export use nogc_async_mut.db.*

# src/lib/gc_async_mut/db/dbfs_engine/__init__.spl
export use nogc_async_mut.db.dbfs_engine.*
```

The same pattern (verified working elsewhere, e.g.
`src/lib/gc_async_immut/__init__.spl: export use std.nogc_async_immut.*`)
is the fix shape needed here — just applied to `compression/` and
`database/sql/` (and likely other affected subsystems below), each getting
a `src/lib/gc_async_mut/<path>/__init__.spl` with `export use
nogc_async_mut.<path>.*`. Not applied in this pass — creating new facade
module files is a multi-file `src/lib/**` addition, out of scope for a
test-triage pass per the fix-guide ("No src/** edits unless the fix is
unambiguously a one-line import/rename").

## Confirmed affected specs (this pass, "Cannot resolve module" signature)

- `test/unit/lib/gc_async_mut/compression/compression_facade_spec.spl` — `std.gc_async_mut.compression.lz4` (and `.zlib`, `.gzip`, `.brotli.encoder/.decoder`)
- `test/unit/lib/gc_async_mut/database/sql/sql_facade_spec.spl` — `std.gc_async_mut.database.sql.escape`

## Likely-same-class, not individually verified this pass

The following `gc_async_mut/**` facade specs from the same triage cluster
were NOT run this pass but share the identical "facade wrapper dir doesn't
exist under gc_async_mut" shape by directory inspection and should be
checked with the same "Cannot resolve module" grep before assuming a
different root cause:

- `database/sql/sql_init_facade_spec.spl`
- `database/test_extended/test_extended_facade_spec.spl`
- `database/vector/database_vector_facade_spec.spl`
- `db/dbfs_engine/dbfs_backend_facade_spec.spl`, `dbfs_checkpoint_attr_facade_spec.spl`, `dbfs_engine_facade_spec.spl` (see Regression note — these three were reportedly fixed 2026-06-11 for the db/dbfs_engine path specifically; re-verify whether `src/lib/gc_async_mut/db/dbfs_engine/__init__.spl` still exists)
- `driver/driver_facade_spec.spl`
- `editor/panels/editor_panels_facade_spec.spl`
- `fs_driver/fs_driver_init_facade_spec.spl`, `nvfs_backend_parity_spec.spl`, `nvfs_driver_facade_spec.spl`
- `fs/nvfs/nvfs_facade_spec.spl`, `fs/nvfs_posix/nvfs_posix_facade_spec.spl`
- `mcp_sdk/core/core_facade_spec.spl`
- `src/collections/src_collections_facade_spec.spl`, `src/core/src_core_facade_spec.spl`, `src/tooling/tooling_facade_spec.spl`
- `storage/shared/storage_shared_facade_spec.spl`
- `text_layout/text_layout_facade_spec.spl`
- `web_ui/web_ui_facade_spec.spl`

Do not assume all of these are "Cannot resolve module" — some may instead be
the RawHandle API-drift bug (`rawhandle_generational_id_api_drift_2026-07-20.md`,
`engine_facade_spec_api_drift_common_types.md`) or the static-method-under-test
landmine (`generic_class_static_method_unresolved_under_test_2026-07-20.md`).
Verify per-spec before filing further docs; this doc only covers the two
confirmed "Cannot resolve module" instances above plus the precedent.

## Regression note (verified 2026-07-20)

`db/dbfs_engine/dbfs_checkpoint_attr_facade_spec.spl` (gc_async_mut tier) was
re-run this pass: the 2026-06-11 module-resolution fix has NOT regressed —
`src/lib/gc_async_mut/db/dbfs_engine/__init__.spl` still exists and the
module resolves fine. It now fails with a DIFFERENT, newer error instead:

```
semantic: function expects argument for parameter 'page_lsn', but none was provided
```

`page_lsn` does not appear literally in the spec file or in
`checkpoint.spl`'s top-level signatures — the missing-argument call is
reached transitively through the facade (likely inside `pager.spl` or
`checkpoint_ring.spl`, not identified further this pass). This is a fresh
API-shape drift unrelated to the facade-module-resolution defect this doc is
about — GENUINE-BUG, needs its own investigation of the dbfs_engine
checkpoint/pager call chain, not filed as a separate doc here since it was
only spot-checked, not root-caused.
