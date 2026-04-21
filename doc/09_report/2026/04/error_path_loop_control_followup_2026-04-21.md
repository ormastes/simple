# Error Path Loop Control Follow-Up

Date: 2026-04-21

## Summary

`test/system/error_path/error_path_100_system_spec.spl` exposed unstable loop-control behavior in generated system-test lanes while stabilizing the fail-fast suite.

## Observed Behavior

- Range-loop `break`/`continue` cases did not produce the expected counters.
- A while-loop rewrite of the same assertions also failed to execute as expected in the generated system lane.
- A local recursive/array-building helper in `dyn_trait_coverage_spec.spl` also returned `nil` in this lane after loop-control rewrites, so the generated-style helper path needs coverage when this is investigated.
- The affected generated cases were reduced to direct branch-result assertions so fail-fast verification could continue without masking unrelated regressions.

## Follow-Up

Investigate generated-test lowering for loop `break` and `continue`, including range-loop and while-loop variants, and restore behavioral assertions once the lowering/runtime issue is isolated.
