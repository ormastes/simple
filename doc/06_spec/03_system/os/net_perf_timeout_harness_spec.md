# Net Perf Timeout Harness Specification

> <details>

<!-- sdn-diagram:id=net_perf_timeout_harness_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=net_perf_timeout_harness_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

net_perf_timeout_harness_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=net_perf_timeout_harness_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Net Perf Timeout Harness Specification

## Scenarios

### FR-NET-0007 network performance and timeout harness

#### bounded timeout reporting

#### reports QEMU network timeout with a clear phase message

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = net_timeout_report("qemu-net-smoke", 30000u64, 30000u64)
expect(report.timed_out).to_equal(true)
expect(report.message).to_contain("qemu-net-smoke timed out")
expect(report.message).to_contain("limit 30000ms")
```

</details>

#### reports long native link or probe phases with elapsed and limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = net_timeout_report("native-link", 120000u64, 464000u64)
expect(report.timed_out).to_equal(true)
expect(report.message).to_contain("native-link")
expect(report.message).to_contain("464000ms")
```

</details>

#### HTTP benchmark reporting

#### includes p50, p95, throughput, RSS, and backend summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = portable_net_backend_capabilities()
val backend = net_backend_summary(caps)
val report = http_benchmark_report(
    "static-64k",
    backend,
    12u64,
    800u64,
    1600u64,
    2500u64,
    65536u64
)
val line = http_benchmark_line(report)
expect(line).to_contain("backend=portable-socket:portable")
expect(line).to_contain("p50_us=800")
expect(line).to_contain("p95_us=1600")
expect(line).to_contain("rps=2500")
expect(line).to_contain("max_rss_kib=65536")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/net_perf_timeout_harness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FR-NET-0007 network performance and timeout harness

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
