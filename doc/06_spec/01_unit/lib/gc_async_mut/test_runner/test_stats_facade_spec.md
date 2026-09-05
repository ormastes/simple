# Test Stats Facade Specification

> Tests covering gc_async_mut test_runner stats facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Stats Facade Specification

## Scenarios

### gc_async_mut test_runner stats facade

#### re-exports deterministic statistics helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports deterministic statistics helpers
   - Expected: stats.count equals `4`
   - Expected: stats.mean equals `25.0`
   - Expected: stats.min equals `10.0`
   - Expected: stats.max equals `40.0`
   - Expected: compute_mean(samples) equals `25.0`
   - Expected: percentiles[0] equals `25.0`
   - Expected: outliers.inliers.len() > 0 is true
   - Expected: has_regression(150.0, 100.0, 10.0, 3.0) is true
   - Expected: has_significant_change(130.0, 100.0, 20.0) is true
   - Expected: detect_flaky_test(10, "pass,fail,pass", 30.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports deterministic statistics helpers")
val samples = [10.0, 20.0, 30.0, 40.0]
val stats = compute_statistics(samples)
expect(stats.count).to_equal(4)
expect(stats.mean).to_equal(25.0)
expect(stats.min).to_equal(10.0)
expect(stats.max).to_equal(40.0)

expect(compute_mean(samples)).to_equal(25.0)
val percentiles = compute_percentiles(samples)
expect(percentiles[0]).to_equal(25.0)

val outliers = detect_outliers_iqr([10.0, 11.0, 12.0, 100.0], 1.5)
expect(outliers.inliers.len() > 0).to_equal(true)
expect(has_regression(150.0, 100.0, 10.0, 3.0)).to_equal(true)
expect(has_significant_change(130.0, 100.0, 20.0)).to_equal(true)
expect(detect_flaky_test(10, "pass,fail,pass", 30.0)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/test_runner/test_stats_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut test_runner stats facade.
- gc_async_mut test_runner stats facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3cee3e052e3d8643f9b73319efc0eea93f3a3c7960b46992904215c31f7a290b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3cee3e052e3d8643f9b73319efc0eea93f3a3c7960b46992904215c31f7a290b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3cee3e052e3d8643f9b73319efc0eea93f3a3c7960b46992904215c31f7a290b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/gc_async_mut/test_runner/test_stats_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/test_runner/test_stats_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/test_runner/test_stats_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/test_runner/test_stats_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/test_runner/test_stats_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/test_runner/test_stats_facade_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports deterministic statistics helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
