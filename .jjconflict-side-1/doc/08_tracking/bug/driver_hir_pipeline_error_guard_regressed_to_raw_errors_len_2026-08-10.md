# `driver_hir_pipeline_passes` error guard regressed to raw `errors.len()` — RED

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 01).
**Filed:** 2026-08-10
**Found by:** repairing the half-landed fix on
`compiler/mono/monomorphize_integration_spec.spl`
(`doc/08_tracking/test/half_landed_fixes_across_duplicate_test_trees_2026-08-10.md`).

## Symptom

`test/01_unit/compiler/mono/monomorphize_integration_spec.spl` and its twin
`test/unit/...` both report `18 total, 17 passed, 1 failed`. The failing example
is `it "checks driver errors before replacing HIR modules"`.

## Why it was invisible

The two test trees both execute. The oracle lived only on the **legacy** leg
(`test/unit/`), and even there it never ran: the legacy leg carried a stale
`use std.test.*`, which fails with `error: semantic: Cannot resolve module:
std.test`, so the whole file reported `executed=0 ... reason=unresolved-module`.
The **numbered** leg (`test/01_unit/`) had the import removed — and the oracle
deleted along with it — so it reported green on `pass`-bodied examples only.

Net effect: one leg could not run the oracle, the other no longer contained it.
The regression below was live and unobserved.

## The defect

`src/compiler/80.driver/driver_hir_pipeline_passes.spl` must guard the
monomorphization pass with `self.ctx.has_errors()` and must not open-code
`self.ctx.errors.len()`. It currently does the opposite:

- line 59: `return self.ctx.errors.len() == 0` (should be `has_errors()`)
- line 66: `self.ctx.errors.len() == 0`
- the spec's `source.index_of("if self.ctx.has_errors():")` therefore returns
  `-1`, and `source.contains("self.ctx.errors.len()")` is `true`.

The ordering assertions (error guard before `run_monomorphization(`, before
`self.ctx.hir_modules = mono_modules`) are the point of the oracle: the driver
must not replace HIR modules after an error.

## Unblock condition

Restore the `has_errors()` guard in
`src/compiler/80.driver/driver_hir_pipeline_passes.spl` so the guard precedes
`run_monomorphization(` and the module assignment, and drop the open-coded
`self.ctx.errors.len()` reads in that function. Then both legs go
`18 total, 18 passed, 0 failed`.

## Do not

Do not delete the oracle, re-add `use std.test.*`, or soften the assertion to
accept `errors.len()`. The spec is correct; the product is not.
