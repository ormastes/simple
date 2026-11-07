# stage2 native-build worker AV: borrowed_trait_providers copied inside live MIR transient scope

- status: fix-implemented-verification-pending
- severity: P0 (bootstrap: stage2 cannot compile a main-only fixture)
- found: 2026-11-07, stage2_new.exe (seed-native build of release 34da19ba4bc)

## Symptom
`native-build` of `test/s3sanity/c01.spl` (main-only) emits 1 object, then the
worker prints `rejected invalid array handle before dereference` and exits
0xC0000005.

## Root cause
`MirLowering.lower_module_transient_scoped` (module_lowering.spl) bound
`val borrowed_trait_providers: [HirModule] = self.trait_impl_provider_modules`
after `transient_array_scope_begin_v1()` and before
`transient_array_scope_pause_v1()`. Native codegen lowers that binding to
`rt_array_copy`, so the copy was an arena allocation; `transient_array_scope_end_v1()`
freed it, and the restore `self.trait_impl_provider_modules = borrowed_trait_providers`
then copied from the dangling handle. lldb: first rejection is
`rt_array_copy` <- `lower_module_transient_scoped+2569` (the restore, right after
`transient_array_scope_end_v1`); the binding copy is at `+0x5aa` before the pause.

Same class as PR #7506 (g_pending_defers via transient scope), different site.

## Fix
Take the borrow after the scope is paused (paused allocations are persistent).

## Tests
- repro: `test/01_unit/compiler/50.mir/transient_scope_borrow_after_pause_spec.spl`
  (fails on the unfixed source at module_lowering.spl:2610).
- prevention: same spec scans all 8 compiler transient-scope owner files for an
  array-typed copy of a `self.`/`g_` root taken while a scope is live and read
  after scope end.
