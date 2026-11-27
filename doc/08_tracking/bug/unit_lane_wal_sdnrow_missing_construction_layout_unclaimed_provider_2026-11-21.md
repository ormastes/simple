# Unit lane: `missing exact struct construction layout 'SdnRow'` (unclaimed provider race)

- **Status:** verification-pending
- **Found:** 2026-11-21, phase-2 xc matrix `linux-x64-test` (frozen Stage 2 `02d3b885266f`, built from release/1.0.0 `25992c96d92`)
- **Symptom:** `MIR lowering error: missing exact struct construction layout 'SdnRow' at .../src/lib/nogc_sync_mut/database/wal.spl:5:1`

## Cause
Per-file units run in an unordered worker pool. `wal.spl` constructs `SdnRow`
(imported from `nogc_sync_mut/database/core.spl`). wal's unit ran before
core's unit had claimed its row (log: `import interface-hir miss reason=no-sidecar`
for core at wal, `hit` for later importers after core's unit ran).
`hir_shard_provider_settle_wait_v1` returned at once for an *unclaimed*
provider, so the import fell back to summary-only (no struct layout rows),
and MIR construction failed closed. Not a MIR layout-registration gap
(#10594/#10595 are in the Stage 2 base); a scheduling race.

## Fix
`hir_shard_provider_settle_wait_v1` (`src/compiler/80.driver/driver_hir_cache.spl`)
also waits for an unclaimed provider listed in the queue's frozen
`inventory` (scheduled work of this build). Unknown providers and finished
providers (`.terminal`) still return at once; the per-unit total budget
(`SIMPLE_UNIT_IMPORT_IFACE_WAIT_MS`, default 60 s) bounds cycles/starvation.
Residual risk: if the provider unit is queued behind a full pool for longer
than the budget, the old fail-closed behaviour returns.

## Tests
`test/01_unit/compiler/80.driver/unit_import_interface_hir_spec.spl`
— "importer waits for an unclaimed provider this build will run" (red before, green after).

## Related, separate
`[parser_error] line 42:54: unexpected token in expression: ->` comes from the
skeleton/surface parser on `std/nogc_sync_mut/io/dir_ops.spl` (also
`secure_memory.spl`, `sha256.spl`; ~44k lines in the log). Not involved here:
`core.spl` has no parser_error. Tracked separately.
