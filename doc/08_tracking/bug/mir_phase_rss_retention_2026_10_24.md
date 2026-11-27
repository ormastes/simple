# Native-build RSS: post-mono dict global and flat HIR store retained through MIR/borrow/codegen (2026-10-24)

Bug id: `mir_phase_rss_retention_2026_10_24`

## Symptom
1471-module bootstrap_main closure, run-9: ~16 GB at mono start, ~33 GB after mono,
36.5 GB at `[mir] 100/1471`, 40.0 GB at `[mir] 1471/1471` (MIR itself only +3.5 GB, ~2.4 MB/module),
then borrow check and codegen OOM.

## Evidence (current producer; static analysis + small probe)
- Probe pa (204 modules, run-pa-after rss series): parent 2.7 GB flat through MIR; MIR worker 1.1 -> 3.6 GB
  across MIR, then 3.6 -> 7.9 GB in the last ~12 s (borrow check/verify), ~21 MB per module.
- Borrow check holds NO cross-module state: `check_mir_module` (55.borrow/borrow_check/mod.spl:835) builds one
  `BorrowChecker` and one `NLLChecker` (nll.spl:398) per function as locals; no globals exist in 55.borrow.
  The growth is allocator/runtime garbage (value-copy of `module.functions[symbol]`, `MirBody.from_function`,
  per-function point/loan dicts), not logical retention; not fixable by eviction here. OPEN.

## Causes fixed (logical retention)
1. `mono_report_modules_owner` (40.mono/monomorphize_integration.spl:4671) is a module global that keeps a
   reference to the whole post-mono `Dict<text, HirModule>` for the rest of the process after
   `driver_hir_pipeline_passes.spl:147` copies it into `ctx.hir_modules`. Any later `ctx.hir_modules` mutation
   (`remove` in go-to-end, `evict_hir`) cannot free the shared storage. Fix: `mono_report_modules_owner_release()`
   called at driver_hir_pipeline_passes.spl:148.
2. Flat HIR store `_bootstrap_hir_module_{names,symbols,functions,constants,enums,structs,classes}`
   (20.hir/hir_lowering/_Items/lowering_helpers.spl:57-74) is a second copy of every module's rows, filled by
   `bootstrap_hir_modules_add_from_module` (driver_hir_pipeline_lowering.spl:1320,1911) and promoted to the
   transient heap. Its only readers are MIR lowering (bootstrap_type_registration.spl, bootstrap_globals.spl:435)
   and the pre-lowering name warm (driver_pipeline_lowering.spl:253). Never reset after MIR in the AOT path
   (`evict_hir` only runs under `low_memory`, which needs SIMPLE_BOOTSTRAP_STAGE4=1). Fix: reset after
   `aot:lower_to_mir:done` (driver_aot_pipeline.spl, `bootstrap_hir_modules_reset()`).

Not done (needs design): `ctx.hir_modules` itself cannot be evicted after MIR, `weave_aop`
(driver_pipeline_aop.spl:48) still reads it; evicting it after weave_aop would save more before codegen.

## Status
Both edits are tagged `@workaround bug=mir_phase_rss_retention_2026_10_24`. They take effect ONLY after a Stage 2
rebuild: all numbers above are from the current producer, the AFTER numbers are PENDING. Expected: removes up to one
HIR-sized copy (the 16 -> 33 GB step is the best candidate, not proven to be fully this) from borrow/codegen.
Unverified: whether transient-heap-promoted rows are returned to the OS by the reset.
No bug-DB row added (sealed sdn); add via `bin/simple bug-add --id=mir_phase_rss_retention_2026_10_24`.
