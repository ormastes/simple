# coverage_unary_not_probe_spec cannot run its collector through `simple test`

Status: OPEN. The spec is tagged `@tag:in-development` until the runner can activate
the collector. Found by the Lunar interpreter sweep (2026-10-30).
Related: `doc/08_tracking/bug/interpreter_coverage_unary_not_leaves_20261011.md`.

## Symptom

`test/01_unit/compiler_core/interpreter/coverage_unary_not_probe_spec.spl` fails
all three examples in a normal run: `expected false to equal true` on
`coverage_enabled()`.

## Root cause

The code under test is correct. The spec needs `SIMPLE_COVERAGE=1` (header line 2),
which turns on the interpreter's global coverage collector. Then it passes 3/3:

    SIMPLE_COVERAGE=1 SIMPLE_EXECUTION_MODE=interpret bin/simple run <spec>
    -> SPEC FILE VERDICT ... executed=3 passed=3 failed=0

There is no working way to give the spec that precondition through `simple test`:
- In a plain run (the sweep), the collector is off, so the precondition fails.
- `SIMPLE_COVERAGE=1 bin/simple test <spec>` turns on the runner's coverage lane
  (`test_runner_single.spl` ~line 1572). That lane requires a Phase 7 child APK
  activation receipt, which the Rust seed never publishes:
  `error: spawned test process did not publish a valid child APK activation receipt`.

## Unblock condition

Do one of these: the runner activates the collector for this spec without
requiring the Phase 7 APK receipt; the seed publishes that receipt; or the
self-hosted binary is deployed. When the lane works, remove the
`@tag:in-development` line from the spec.
