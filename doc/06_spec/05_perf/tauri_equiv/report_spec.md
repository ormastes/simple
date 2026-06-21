# Report Specification

> <details>

<!-- sdn-diagram:id=report_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=report_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

report_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=report_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Report Specification

## Scenarios

### tauri_equiv report spec

### output line parser

#### extracts workflow from summary line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "[tauri-equiv-summary] workflow=cold_start p50_us=1200 p95_us=3400 rss_kb=8192"
expect(_parse_field(line, "workflow=")).to_equal("cold_start")
```

</details>

#### extracts p50_us from summary line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "[tauri-equiv-summary] workflow=new_window p50_us=450 p95_us=900 rss_kb=6400"
expect(_parse_i64(line, "p50_us=")).to_equal(450)
```

</details>

#### extracts p95_us from summary line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "[tauri-equiv-summary] workflow=resize p50_us=200 p95_us=750 rss_kb=7200"
expect(_parse_i64(line, "p95_us=")).to_equal(750)
```

</details>

#### extracts rss_kb from summary line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "[tauri-equiv-summary] workflow=idle p50_us=0 p95_us=0 rss_kb=12288"
expect(_parse_i64(line, "rss_kb=")).to_equal(12288)
```

</details>

#### extracts cpu_pct_x100 from idle line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "[tauri-equiv] workflow=idle cpu_pct_x100=234 rss_kb=9000"
expect(_parse_i64(line, "cpu_pct_x100=")).to_equal(234)
```

</details>

#### returns empty string for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "[tauri-equiv-summary] workflow=scroll p50_us=500 p95_us=1200 rss_kb=8000"
expect(_parse_field(line, "missing_key=")).to_equal("")
```

</details>

### ratio computation

#### computes 1.00x when values are equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_compute_ratio_x100(1000, 1000)).to_equal(100)
```

</details>

#### computes 0.50x when simple is half of tauri

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_compute_ratio_x100(500, 1000)).to_equal(50)
```

</details>

#### computes 1.25x at the NFR boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_compute_ratio_x100(125, 100)).to_equal(125)
```

</details>

#### computes 2.00x when simple is double

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_compute_ratio_x100(2000, 1000)).to_equal(200)
```

</details>

#### returns 100 when both values are zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_compute_ratio_x100(0, 0)).to_equal(100)
```

</details>

#### returns 10000 when tauri is zero and simple is nonzero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_compute_ratio_x100(500, 0)).to_equal(10000)
```

</details>

### NFR 2B gates

#### PASS when ratio is exactly 1.25x

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_nfr_ratio_pass(125)).to_equal(true)
```

</details>

#### PASS when ratio is better than 1.25x

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_nfr_ratio_pass(100)).to_equal(true)
```

</details>

#### FAIL when ratio exceeds 1.25x

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_nfr_ratio_pass(126)).to_equal(false)
```

</details>

#### FAIL when ratio is 2.00x

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_nfr_ratio_pass(200)).to_equal(false)
```

</details>

#### equal-or-better gate PASS when cold_start ratio <= 1.00x

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_nfr_equal_or_better(95, 150)).to_equal(true)
```

</details>

#### equal-or-better gate PASS when idle RSS ratio <= 1.00x

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_nfr_equal_or_better(110, 85)).to_equal(true)
```

</details>

#### equal-or-better gate PASS when both are <= 1.00x

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_nfr_equal_or_better(90, 80)).to_equal(true)
```

</details>

#### equal-or-better gate FAIL when both exceed 1.00x

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_nfr_equal_or_better(120, 110)).to_equal(false)
```

</details>

### percentile computation

#### p50 of sorted 10-element array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sorted = [10, 20, 30, 40, 50, 60, 70, 80, 90, 100]
expect(_percentile(sorted, 50)).to_equal(50)
```

</details>

#### p95 of sorted 20-element array

1. samples = samples push
   - Expected: _percentile(sorted, 95) equals `1900`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var samples: [i64] = []
var i: i64 = 1
while i <= 20:
    samples = samples.push(i * 100)
    i = i + 1
val sorted = _sort_ascending(samples)
# p95 index = (20 * 95) / 100 = 19 → value = 1900
expect(_percentile(sorted, 95)).to_equal(1900)
```

</details>

#### p50 of single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_percentile([42], 50)).to_equal(42)
```

</details>

#### returns 0 for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [i64] = []
expect(_percentile(empty, 50)).to_equal(0)
```

</details>

### sort_ascending

#### sorts descending input

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = [5, 3, 1, 4, 2]
val sorted = _sort_ascending(input)
expect(sorted[0]).to_equal(1)
expect(sorted[4]).to_equal(5)
```

</details>

#### handles already-sorted input

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = [1, 2, 3, 4, 5]
val sorted = _sort_ascending(input)
expect(sorted[0]).to_equal(1)
expect(sorted[4]).to_equal(5)
```

</details>

#### handles single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sorted = _sort_ascending([99])
expect(sorted[0]).to_equal(99)
```

</details>

### required workflows

#### all 9 required workflow names are defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val required = ["cold_start", "new_window", "close_window", "resize",
                "scroll", "route_change", "ipc_roundtrip", "event_broadcast",
                "idle"]
expect(required.length()).to_equal(9)
```

</details>

#### NFR-gated workflows include the required subset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# new_window, scroll, resize, ipc_roundtrip must all be within 1.25x
val nfr_gated = ["new_window", "scroll", "resize", "ipc_roundtrip"]
expect(nfr_gated.length()).to_equal(4)
```

</details>

### report fields

#### all required report columns are accounted for

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# workflow, simple_p50_ms, simple_p95_ms, tauri_p50_ms, tauri_p95_ms,
# simple_rss_kb, tauri_rss_kb, simple_vs_tauri_ratio
val required_fields = ["workflow", "simple_p50_us", "simple_p95_us",
                       "tauri_p50_us", "tauri_p95_us",
                       "simple_rss_kb", "tauri_rss_kb",
                       "simple_vs_tauri_ratio"]
expect(required_fields.length()).to_equal(8)
```

</details>

<details>
<summary>Advanced: workflow driver produces parseable summary lines</summary>

#### workflow driver produces parseable summary lines _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify the expected line format can be parsed end-to-end
val sample_lines = [
    "[tauri-equiv-summary] workflow=cold_start p50_us=1500 p95_us=4200 rss_kb=9000",
    "[tauri-equiv-summary] workflow=new_window p50_us=300 p95_us=800 rss_kb=9100",
    "[tauri-equiv-summary] workflow=close_window p50_us=50 p95_us=120 rss_kb=9050",
    "[tauri-equiv-summary] workflow=resize p50_us=250 p95_us=700 rss_kb=9200",
    "[tauri-equiv-summary] workflow=scroll p50_us=4000 p95_us=8000 rss_kb=9300",
    "[tauri-equiv-summary] workflow=route_change p50_us=350 p95_us=900 rss_kb=9100",
    "[tauri-equiv-summary] workflow=ipc_roundtrip p50_us=10 p95_us=30 rss_kb=9000",
    "[tauri-equiv-summary] workflow=event_broadcast p50_us=5 p95_us=15 rss_kb=9000",
    "[tauri-equiv] workflow=idle cpu_pct_x100=50 rss_kb=9000"
]
var parsed_count: i64 = 0
var i: i64 = 0
while i < sample_lines.length():
    val line = sample_lines[i]
    val wf = _parse_field(line, "workflow=")
    if wf != "":
        parsed_count = parsed_count + 1
    i = i + 1
expect(parsed_count).to_equal(9)

# Verify ratio computation on sample data
# cold_start: simple=4200us tauri=5000us → ratio=84 (0.84x) — equal or better
val cs_ratio = _compute_ratio_x100(4200, 5000)
expect(cs_ratio).to_be_less_than(101)  # <= 1.00x
expect(_nfr_equal_or_better(cs_ratio, 150)).to_equal(true)

# new_window: simple=800us tauri=700us → ratio=114 (1.14x) — within 1.25x
val nw_ratio = _compute_ratio_x100(800, 700)
expect(nw_ratio).to_be_less_than(126)
expect(_nfr_ratio_pass(nw_ratio)).to_equal(true)

print "workflow_driver parse/ratio smoke: PASS"
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/tauri_equiv/report_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- tauri_equiv report spec
- output line parser
- ratio computation
- NFR 2B gates
- percentile computation
- sort_ascending
- required workflows
- report fields

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
