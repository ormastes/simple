# Nginx Compare Harness Specification

> Verifies that the nginx-vs-Simple benchmark harness produces deterministic fixtures, accepts labelled configs, captures all required metrics (p99 latency, RPS, throughput, failure count), and formats valid SDN reports.

<!-- sdn-diagram:id=nginx_compare_harness_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nginx_compare_harness_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nginx_compare_harness_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nginx_compare_harness_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nginx Compare Harness Specification

Verifies that the nginx-vs-Simple benchmark harness produces deterministic fixtures, accepts labelled configs, captures all required metrics (p99 latency, RPS, throughput, failure count), and formats valid SDN reports.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Performance |
| Status | Active |
| Source | `test/01_unit/perf/nginx_compare_harness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Verifies that the nginx-vs-Simple benchmark harness produces deterministic
fixtures, accepts labelled configs, captures all required metrics (p99 latency,
RPS, throughput, failure count), and formats valid SDN reports.

## Key Concepts
- Fixture tiers: small (1 KB), medium (64 KB), large (1 MB)
- Server labels: "simple" or "nginx"
- SDN report format compatible with doc/10_metrics/ dashboard tables

## Scenarios

### FixtureGenerator

#### tier definitions

#### has small tier at 1024 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sizes = fixture_tier_sizes()
expect(sizes[0]).to_equal(1024)
```

</details>

#### has medium tier at 65536 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sizes = fixture_tier_sizes()
expect(sizes[1]).to_equal(65536)
```

</details>

#### has large tier at 1048576 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sizes = fixture_tier_sizes()
expect(sizes[2]).to_equal(1048576)
```

</details>

#### produces exactly three tiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sizes = fixture_tier_sizes()
expect(sizes.len()).to_equal(3)
```

</details>

### BenchmarkConfig

#### server labels

#### accepts simple label

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val label = make_config("simple")
expect(label).to_equal("simple")
```

</details>

#### accepts nginx label

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val label = make_config("nginx")
expect(label).to_equal("nginx")
```

</details>

### BenchmarkResult

#### metric fields

#### captures rps

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = make_result("simple", 1234.5, 2.50, 10.0, 0, 1024, "2026-05-26T00:00:00Z")
expect(summary).to_contain("rps=1234.5")
```

</details>

#### captures p99 latency

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = make_result("simple", 0.0, 4.99, 0.0, 0, 1024, "2026-05-26T00:00:00Z")
expect(summary).to_contain("p99=4.99")
```

</details>

#### captures throughput

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = make_result("nginx", 0.0, 0.0, 55.5, 0, 65536, "2026-05-26T00:00:00Z")
expect(summary).to_contain("tp=55.5")
```

</details>

#### captures failure count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = make_result("simple", 0.0, 0.0, 0.0, 42, 1024, "2026-05-26T00:00:00Z")
expect(summary).to_contain("failures=42")
```

</details>

#### captures server label

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = make_result("nginx", 0.0, 0.0, 0.0, 0, 1024, "2026-05-26T00:00:00Z")
expect(summary).to_start_with("server=nginx")
```

</details>

#### captures timestamp

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = make_result("simple", 0.0, 0.0, 0.0, 0, 1024, "2026-05-26T00:00:00Z")
expect(summary).to_contain("ts=2026-05-26T00:00:00Z")
```

</details>

#### captures file size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = make_result("simple", 0.0, 0.0, 0.0, 0, 1048576, "2026-05-26T00:00:00Z")
expect(summary).to_contain("size=1048576")
```

</details>

### SDNReportFormatter

#### header format

#### starts with the table name and column list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hdr = make_sdn_header()
expect(hdr).to_start_with("nginx_compare |")
```

</details>

#### contains all required columns

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hdr = make_sdn_header()
expect(hdr).to_contain("rps")
expect(hdr).to_contain("p99_latency_ms")
expect(hdr).to_contain("throughput_mbps")
expect(hdr).to_contain("failure_count")
expect(hdr).to_contain("timestamp")
expect(hdr).to_contain("server")
```

</details>

#### row format

#### produces indented rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = make_sdn_row(1, "simple", 1024, "1KB", "2026-05-26T00:00:00Z")
expect(row).to_start_with("    ")
```

</details>

#### quotes string fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = make_sdn_row(1, "simple", 1024, "1KB", "2026-05-26T00:00:00Z")
expect(row).to_contain("\"simple\"")
expect(row).to_contain("\"1KB\"")
```

</details>

#### includes the file size as integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = make_sdn_row(1, "nginx", 65536, "64KB", "2026-05-26T00:00:00Z")
expect(row).to_contain("65536")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
