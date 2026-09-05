# rt_hal_tag_retention_spec: two pre-existing RED cases after helper repair

**Date:** 2026-08-28 · **Spec:** `test/01_unit/compiler/frontend/rt_hal_tag_retention_spec.spl`
**Found by:** impl_C (dual-run lane) while widening `validate_rt_hal_tags`.

## State at release tip f92fa0bb4d5

The spec could not run at all: its helpers called `HirLowering.lower_module`
without `use compiler.hir.hir_lowering.items.*` (where the extension lives)
and `MirLowering.new(hir.symbols)`, an API that no longer exists
(`MirLowering.new_for_target(symbols, target_context)` is current). Every
case died with `semantic: method lower_module not found` — the file was
green-looking only because nobody ran it.

## Fixed in this lane

Imports repaired (`hir_lowering.items.*`, `mir_lowering_types.{MirLowering}`,
`_MirLowering.module_lowering.*`, `driver_mir_target_context`) and the MIR
helper moved to `new_for_target`. Result: `Results: 10 total, 8 passed, 2 failed`
(seed binary; at the base the file reported `8 failed` with only the two
metadata-retention cases passing, every lowering/validator case dying on the
missing `lower_module`). The three new validator cases
(typed args accepted; `Dict` param rejected naming `ports`; `[i64]` rejected as
"not u8") and the Pure-only ABI case are GREEN.

## Still RED — NOT weakened, left for the owner of `module_assembly.spl` / `mir_rt_hal_boundary.spl`

1. `defaults to Pure Simple without comparator flags` — expects **no**
   `std.nogc_sync_mut.rt_hal.boundary` import for a Pure-only `@rt(hal)`
   function. `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:1102-1111`
   pushes that import for **every** `is_rt_hal` function, comparator or not.
   Either the spec's expectation or the bridge is stale; the bridge comment
   says "only modules whose retained FunctionAttr contains @rt(hal) acquire
   the runtime boundary dependency", which is what it does — the spec wants
   the narrower comparator-only rule. Decide, then fix one side.
2. `lowers only an RT-safe receipt enqueue at each normal exit` — the
   `rt_hal_lowered_calls` helper walks `mir.functions[*].blocks[*].instructions`
   looking for `MirInstKind.Call(_, callee, _)` with a `Const(Str(name))`
   callee and finds **none** for `@rt(hal, c) fn clock_read() -> i64`. Either
   the boundary lowering (`50.mir/mir_rt_hal_boundary.spl`) no longer runs in
   `new_for_target` lowering without extra setup, or the callee is no longer a
   string constant. Unblock condition: print the MIR of that fixture and
   match the helper to the real instruction shape. Measured 2026-08-28:
   `inject_rt_hal_boundary` (`mir_rt_hal_boundary.spl:36`) has **no caller**
   outside its own module; the pure pipeline only calls
   `inject_rt_hal_worker_complete` from
   `_MirLoweringExpr/switch_operators_calls.spl:4461`, gated on
   `rt_hal_compilation_requires_finalize()` — which `validate_rt_hal_tags`
   sets only when a comparator (`c`/`rust`) is requested. So the receipt
   lowering is already comparator-scoped; the validator's new scoping (a
   Pure-only `@rt(hal)` ABI needs no i64 receipt) introduces no miscompile,
   and the spec's `rt_hal_boundary_dispatch` expectation targets an injector
   that is wired to nothing.

Neither case touches `validate_rt_hal_tags`; both were unreachable before this
lane repaired the helpers.
