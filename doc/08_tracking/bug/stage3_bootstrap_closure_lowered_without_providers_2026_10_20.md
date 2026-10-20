# Stage 3 bootstrap-fixed closure modules lowered with no providers (47,497 MIR errors)

- Status: FIX COMMITTED; probe validated (0 MIR errors), full-closure MIR result pending
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

The entry module (`lower_bootstrap_entry_module`) gets the same feed
(Opus review): with `[]` it kept this error class for
`app.cli.bootstrap_main` and saw composite metadata relocated against the
last closure module's symbols.

## Validation (2026-10-20, aarch64, diagnostic relink `s2diag17` sha256 61f1f47a37bc...)

- Probe Stage 3 (entry importing a struct, method, `pub fn` and two
  imported `pub val`s from two closure modules): MIR lowering 0 errors
  (was the 47k class). The run then stops in real-LLVM codegen on an
  unrelated defect:
  `stage3_bootstrap_real_llvm_imported_global_undeclared_2026_10_20.md`.
- Full diagnostic Stage 3 on the r8-based tree (no upstream provider-walk
  perf chain a92edd2fb7b/6c15637b026/cc601e8f3d3/c4da3f8d8e4):
  12.8 s per closure module, flat over 90 modules (4.7 modules/min);
  `s4_promote_*` (#3925) is 167 ms of that, the rest is per-module provider
  registration. heap_live grows linearly, 7.5-9.0 MB per module
  (3.78 GB at module 10, 4.44 GB at module 90); RSS 27.4 GB.
