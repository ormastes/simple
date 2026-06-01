# Pure Smf Dynlib Perf Specification

## Scenarios

### pure GUI SMF dynlib perf contract

#### computes p50 p95 p99 and max from measured samples

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = gui_dynlib_perf_stats([100, 700, 300, 900, 200])
expect(stats.p50_us).to_equal(300)
expect(stats.p95_us).to_equal(900)
expect(stats.p99_us).to_equal(900)
expect(stats.max_us).to_equal(900)
```

</details>

#### passes only real smf dynlib samples below one millisecond

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = gui_dynlib_perf_report(
    "build/gui/pure_gui.smf",
    "smf_dynlib",
    "gui_dynlib_hot_probe_tick",
    "dynlib_symbol_call",
    true,
    false,
    100,
    [180, 220, 240, 300, 410, 640, 720, 810, 900, 990],
    1000
)
expect(report.pass).to_equal(true)
expect(report.error).to_equal("")
expect(report.stats.p99_us).to_equal(990)
```

</details>

#### rejects interpreter or fallback measurements

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = gui_dynlib_perf_report(
    "build/gui/pure_gui.smf",
    "interpreter",
    "gui_dynlib_hot_probe_tick",
    "direct_simple",
    true,
    false,
    100,
    [100],
    1000
)
expect(report.pass).to_equal(false)
expect(report.error).to_equal("not-smf-dynlib")
```

</details>

#### rejects unresolved dynlib symbols

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = gui_dynlib_perf_report(
    "build/gui/pure_gui.smf",
    "smf_dynlib",
    "gui_dynlib_hot_probe_tick",
    "dynlib_symbol_call",
    false,
    false,
    100,
    [100],
    1000
)
expect(report.pass).to_equal(false)
expect(report.error).to_equal("symbol-not-resolved")
```

</details>

#### rejects p99 at one millisecond or above

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = gui_dynlib_perf_report(
    "build/gui/pure_gui.smf",
    "smf_dynlib",
    "gui_dynlib_hot_probe_tick",
    "dynlib_symbol_call",
    true,
    false,
    100,
    [100, 1000],
    1000
)
expect(report.pass).to_equal(false)
expect(report.error).to_equal("p99-over-threshold")
```

</details>

#### emits a machine-readable evidence row

<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = gui_dynlib_perf_report(
    "build/gui/pure_gui.smf",
    "smf_dynlib",
    "gui_dynlib_hot_probe_tick",
    "dynlib_symbol_call",
    true,
    false,
    100,
    [100],
    1000
)
val row = gui_dynlib_perf_report_row(report)
expect(row.contains("GUI_DYNLIB_PERF")).to_equal(true)
expect(row.contains("loader=smf_dynlib")).to_equal(true)
expect(row.contains("call_source=dynlib_symbol_call")).to_equal(true)
expect(row.contains("p99_us=100")).to_equal(true)
```

</details>

#### rejects direct in-process hot calls even with a resolved symbol

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = gui_dynlib_perf_report(
    "build/gui/pure_gui.smf",
    "smf_dynlib",
    "gui_dynlib_hot_probe_tick",
    "direct_simple",
    true,
    false,
    100,
    [100],
    1000
)
expect(report.pass).to_equal(false)
expect(report.error).to_equal("not-dynlib-hot-call")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gui/pure_smf_dynlib_perf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- pure GUI SMF dynlib perf contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

