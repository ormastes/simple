# Test runner execution API export drift

- id: test_runner_execution_export_drift_2026-10-31
- found: bootstrap runner build investigation, 2026-10-31
- source baseline: `98f8c0807b39`
- status: two narrow export repairs and caller-based regressions authored;
  runtime qualification UNRUN

## Caller chain and defects

The safe-mode implementation is
`nogc_sync_mut.test_runner.test_runner_execute.run_test_file_safe_mode`.
Real callers use that name, but the sync execute module's export list exposes
only the stale `run_test_file_safe`. The async execute facade wildcard
re-exports the sync module, so an explicit async import of the actual safe-mode
function also fails. Repair the existing export entry to name
`run_test_file_safe_mode`; add no alias, stub, or new function.

The synchronous doctest implementation and consumers use
`should_fail_infra_reason`, defined by
`nogc_sync_mut.test_runner.sdoctest.types`. The async `sdoctest.types` facade
explicitly reexports the shared records and enums but omits this helper.
Reexport the existing sync-owned function from that facade without duplicating
its classification logic.

## Evidence and limits

The source baseline for this repair is `98f8c0807b39`. The prior runner
attempt warned about unresolved export origins and possible later unresolved
names, then terminated on timeout 124; a terminal semantic error was not proven.
These two export defects are confirmed API drift;
they do not establish that the entire runner build will succeed after repair or
prove that they were the sole cause of the timeout.

`test/01_unit/lib/test_runner/runner_execution_export_contract_spec.spl`
invokes the real safe-mode API through the async facade with an unsupported
compiler selector, exercises the actual async classification facade, and
calls the production synchronous doctest result classifier directly. These
tests are authored but **UNRUN**; no RED/GREEN, link, build, or execution result
is claimed.

## Qualification gate

Completion requires an exact frozen repaired source and an admitted producer
that can link and execute the actual standalone runner. Static export checks
and these authored tests do not satisfy that gate. Preserve the distinction
between this source repair and the unresolved prior timeout investigation.
