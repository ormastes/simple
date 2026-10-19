# Stage 3 bootstrap-fixed closure modules lowered with no providers (47,497 MIR errors)

- Status: FIX COMMITTED (source); native validation pending
- Date: 2026-10-20
- Platform: aarch64-unknown-linux-gnu

## Observation

Diagnostic Stage 3 (relinked Stage 2 `9ad2504c...`, tree 9ff6a6182c8) got
through HIR, monomorphization and the whole closure loop at flat RSS
(29.9 GB), then MIR failed with 47,497 errors attributed to
`app.cli.bootstrap_main`, spanning src/app, src/compiler and src/lib:

- 15,620 `array return record element has no unique provider layout`
- `unresolved method call: next_i64` (2,934), `put_text`, `next`, `put_i64`,
  `add_error`, `error_fatal`, `emit_call`, `get_symbol_raw`, `new_temp`, ...
- `missing provider declaration for imported global
  'lib.nogc_sync_mut.compression.gzip.types::BLOCK_DYNAMIC'` and
  `undefined variable BLOCK_STORED/BLOCK_FIXED/BLOCK_DYNAMIC`

## Cause

The closure loop added by 31cb5365440 lowered every closure module with an
empty provider list (`lower_module(hir, [], false)`, later
`lower_bootstrap_closure_module(hir)`), so no cross-module method, record
layout or imported global could resolve. The direct lane passes the
whole-closure HIR feed `ctx.mir_feed_modules`
(driver_pipeline_lowering.spl:666-669), built before the bootstrap-fixed
branch runs.

## Fix

`lower_bootstrap_closure_module(module, providers)` forwards the driver's
`self.ctx.mir_feed_modules` (by reference) into
`lower_module_transient_scoped`; the transient scope still covers only the
per-module scratch.
