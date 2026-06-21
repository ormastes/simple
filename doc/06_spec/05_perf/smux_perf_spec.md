# Smux Perf Specification

> <details>

<!-- sdn-diagram:id=smux_perf_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smux_perf_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smux_perf_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smux_perf_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smux Perf Specification

## Scenarios

### smux performance smoke

<details>
<summary>Advanced: keeps reset plus initial session startup under the hosted smoke budget</summary>

#### keeps reset plus initial session startup under the hosted smoke budget _(slow)_

1. samples = samples push


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# warmup
var w = 0
while w < 3:
    val _ = _simulate_startup_ns()
    w = w + 1

# measure
var samples: [i64] = []
var m = 0
while m < 20:
    samples = samples.push(_simulate_startup_ns())
    m = m + 1

val avg_ms = _average(samples) / 1000000
val p95_ms = _percentile(samples, 95, 100) / 1000000
val iters = samples.len()
print "[perf] smux startup avg={avg_ms}ms p95={p95_ms}ms iters={iters}"
expect(avg_ms).to_be_less_than(200)
expect(p95_ms).to_be_less_than(200)
```

</details>


</details>

<details>
<summary>Advanced: keeps send plus capture p95 within the interactive smoke budget</summary>

#### keeps send plus capture p95 within the interactive smoke budget _(slow)_

1. samples2 = samples2 push


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# warmup
var w2 = 0
while w2 < 5:
    val _ = _simulate_send_capture_ns()
    w2 = w2 + 1

# measure
var samples2: [i64] = []
var seq = 0
while seq < 50:
    samples2 = samples2.push(_simulate_send_capture_ns())
    seq = seq + 1

val avg_ms2 = _average(samples2) / 1000000
val p95_ms2 = _percentile(samples2, 95, 100) / 1000000
val iters2 = samples2.len()
print "[perf] smux send/capture avg={avg_ms2}ms p95={p95_ms2}ms iters={iters2}"
expect(avg_ms2).to_be_less_than(20)
expect(p95_ms2).to_be_less_than(20)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/smux_perf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- smux performance smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 2 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
