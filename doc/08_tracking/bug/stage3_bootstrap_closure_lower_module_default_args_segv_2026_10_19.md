# Stage 3 bootstrap-fixed closure loop SIGSEGVs in lower_module (omitted default args)

- Status: FIX COMMITTED (source); native validation pending a Stage 2 rebuild
- Date: 2026-10-19
- Platform: aarch64-unknown-linux-gnu
- Blocks: Stage 3 MIR lowering, right after
  `aot:bootstrap_fixed:start module=app.cli.bootstrap_main functions=30`.

## Observation

Stage 3 r14 (admitted Stage 2 sha256 `dad7e0ce...13c4`) passed HIR
(1316/1316, cache hits 1316), rt_criticality validation (errors=0),
typecheck and monomorphization, then died with signal 11 before the first
`aot:bootstrap_fixed:closure_module` line. Core (apport, unpacked):

```text
#0 MirLowering.lower_module+804   ldr x23, [x8, #8]   x8 = 0xfffffffffffffff0
#1 CompilerDriver.lower_to_mir_with_target_context
#2 CompilerDriver.lower_to_mir
#3 CompilerDriver.aot_compile
```

`lower_module+788..804` is `rt_for_iterable(x20)` with `x20 = x6`, the
seventh argument: `archive_trait_thunks: [MirFunction] = []`. The caller is
the closure loop added by 31cb5365440
(`driver_pipeline_lowering.spl:946`), which calls
`bootstrap_lowering.lower_module(bootstrap_closure_hir, [], false)` from
another module and omits the three trailing defaulted parameters
(`archive_function_symbols`, `archive_primary_globals`,
`archive_trait_thunks`). The seed-compiled Stage 2 passes garbage for them.
This is the same call-shape class as
`stage3_bootstrap_fixed_lower_module_segv_2026-10-11.md` (a0d60244575).

## Fix

`MirLowering.lower_bootstrap_closure_module(module)` forwards all six
arguments explicitly from inside the class; the driver calls it.
`lower_bootstrap_entry_module` now also forwards all six (it omitted the
same three archive defaults). The underlying seed defect -- cross-module
calls with omitted defaulted parameters receive garbage -- remains open.
