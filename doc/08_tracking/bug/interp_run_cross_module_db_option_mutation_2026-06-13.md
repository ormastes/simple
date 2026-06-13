# BUG: `bin/simple run` (interpreter) loses cross-module DB Option/struct returns + field mutations

- **ID:** `interp_run_cross_module_db_option_mutation`
- **Severity:** P1 (db unusable from a cross-module interpreter `run` driver; works in compiled `test`)
- **Found:** 2026-06-13, perf-umbrella db benchmark driver (AC-5 emit).
- **Distinct from** `interp_unit_param_keyword_collision` (the `unit` keyword bug — already fixed).
  Related to memory `feedback_cross_module_mutation_loss` ("free fn(self: Class) across modules
  loses field mutations; use me-methods + extension impl").

## Symptom
Driving the pure-Simple DB from a separate-module `fn main()` via `bin/simple run`:
- `PureDatabase.memory()` / `open_deferred()` struct/Option return resolves as `None`/empty in the
  caller module → `.unwrap()` panics (ram + persistent configs).
- `MvccTable.insert()` + `mgr.commit()` mutations are silently lost across the module boundary →
  `count_visible()` returns 0 instead of N (wal config).
The SAME db spec passes 13/13 under `bin/simple test` (compiled mode).

## Impact
- AC-5 db benchmark emission (`db_bench_driver.spl`) omits all three mode rows in interpreter
  `run` mode (honest omission, reasons printed — no fabricated numbers). The db spec's correctness
  assertions still pass in compiled `test` mode.

## Repro
`bin/simple run test/05_perf/db/db_bench_driver.spl` → all rows omitted with printed reasons.
Minimal: a 2-module program where module B calls `PureDatabase.memory()` from module A and inserts.

## Proposed next step (staged)
1. Minimal 2-module repro under `test/fixtures/` (Option return + self-mutation across modules).
2. Locate: interpreter executor cross-module value/Option boxing + receiver-mutation handling
   (likely Rust seed — confirm; if seed, scope a change like the `unit` fix).
3. Workaround meanwhile: emit db benchmark numbers from compiled (`test`/smf/native) mode, or keep
   db construction + use in one module.

## Status
OPEN — staged. db benchmark doc emits with honest omitted rows; correctness covered in compiled mode.
