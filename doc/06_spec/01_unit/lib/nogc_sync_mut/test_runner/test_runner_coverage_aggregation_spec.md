# Cross-Process Coverage Aggregation Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 2 | 2 | 0 | 0 |

## Purpose

Proves that decision outcomes emitted by separate test children are retained by
the parent coverage collector and that an aggregate percentage cannot hide a
file below its declared `# @cover` threshold.

## Scenario

### merges true and false outcomes retained by separate child runs

1. Reset the parent coverage collector.
2. Record one child SDN with the true outcome.
3. Record another child SDN with the false outcome.
4. Collect the merged coverage report.
5. Require one file, one decision, and 100% decision coverage.

<details>
<summary>Executable SSpec</summary>

Source: `test/01_unit/lib/nogc_sync_mut/test_runner/test_runner_coverage_aggregation_spec.spl`

```simple
# @cover src/lib/nogc_sync_mut/test_runner/test_runner_coverage.spl 100%

use std.spec.*
use std.test_runner.test_runner_coverage.{
    collect_coverage,
    record_coverage_sdn,
    reset_coverage_state
}

fn child_decision_sdn(true_count: i64, false_count: i64) -> text:
    "decisions |id, file, line, column, true_count, false_count|\n" +
        "    branch-1, src/owned/frame.spl, 10, 4, {true_count}, {false_count}\n" +
        "conditions |decision_id, condition_id, file, line, column, true_count, false_count|"

describe "cross-process coverage aggregation":
    it "merges true and false outcomes retained by separate child runs":
        reset_coverage_state()
        record_coverage_sdn(child_decision_sdn(1, 0))
        record_coverage_sdn(child_decision_sdn(0, 1))

        val coverage = collect_coverage()
        expect(coverage.files.len()).to_equal(1)
        expect(coverage.files[0].path).to_equal("src/owned/frame.spl")
        expect(coverage.files[0].decisions_total).to_equal(1)
        expect(coverage.files[0].decisions_covered).to_equal(1)
        expect(coverage.files[0].decision_pct).to_equal(100)
        expect(coverage.total_decisions).to_equal(1)
        expect(coverage.total_decisions_covered).to_equal(1)
        expect(coverage.decision_pct).to_equal(100)
        reset_coverage_state()
```

</details>

### rejects an owner below its annotated threshold despite 99 percent aggregate coverage

1. Record 100 decisions: 99 covered overall, but only one of two covered for
   `src/owned/frame.spl`.
2. Require the owner's `50%` annotation to pass and its `100%` annotation to
   fail.
3. Require missing targets and malformed percentages, including numeric-prefix
   forms such as `50junk%` and `50%%`, to fail closed.

The executable assertions are in
`test/01_unit/lib/nogc_sync_mut/test_runner/test_runner_coverage_aggregation_spec.spl`.

## Evidence Status

The scenario contains real assertions and no placeholder pass. Its diagnostic
run timed out before a result on the available unaccepted runtime, so this
manual records source-ready coverage infrastructure rather than a PASS or a
measured whole-feature coverage percentage.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Unit / test runner |
| Status | Active; runtime execution blocked |
| Source | `test/01_unit/lib/nogc_sync_mut/test_runner/test_runner_coverage_aggregation_spec.spl` |
| Updated | 2026-07-27 |
| Manual | Maintained after bounded docgen timeout |
