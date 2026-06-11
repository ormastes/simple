# Timing Facade Specification

> <details>

<!-- sdn-diagram:id=timing_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=timing_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

timing_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=timing_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Timing Facade Specification

## Scenarios

### gc_async_mut timing facade

#### re-exports timing record types without depending on wall-clock assertions

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val start = Instant(micros: 1000)
expect(start.micros).to_equal(1000)

val profile = ProfileResult(elapsed_ms: 2, elapsed_micros: 2500)
expect(profile.elapsed_ms).to_equal(2)
expect(profile.elapsed_micros).to_equal(2500)

val bench = BenchmarkResult(iterations: 3, total_ms: 9, avg_ms: 3.0, min_ms: 2, max_ms: 4)
expect(bench.iterations).to_equal(3)
expect(bench.avg_ms).to_equal(3.0)
expect(bench.max_ms).to_equal(4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/timing_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut timing facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
