# Test Extended Facade Specification

> <details>

<!-- sdn-diagram:id=test_extended_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_extended_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_extended_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_extended_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Extended Facade Specification

## Scenarios

### gc_async_mut database test_extended facade

#### re-exports records and host stub helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val counter = CounterRecord(
    test_id: 7, total_runs: 3, passed: 2, failed: 1,
    crashed: 0, timed_out: 0, flaky_count: 0, consecutive_passes: 1
)
val timing = TimingSummary(
    test_id: 7, mean: 10.0, p50: 9.0, p90: 12.0, p95: 13.0,
    p99: 14.0, iqr: 2.0, has_baseline: true,
    baseline_p50: 9.0, baseline_updated_at: "now", last_10_runs: "[]"
)

expect(counter.total_runs).to_equal(3)
expect(timing.has_baseline).to_equal(true)
expect(rt_getpid()).to_be_greater_than(0)
expect(hostname()).to_equal("localhost")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/database/test_extended/test_extended_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut database test_extended facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
