# Glass Pixel Compare Specification

> <details>

<!-- sdn-diagram:id=glass_pixel_compare_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=glass_pixel_compare_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

glass_pixel_compare_spec -> std
glass_pixel_compare_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=glass_pixel_compare_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Glass Pixel Compare Specification

## Scenarios

### Glass pixel comparison — single demo

#### renders minimal.ui.sdn through both pipelines without error

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = render_both_pipelines(
    "examples/06_io/ui/minimal.ui.sdn", "glass_dark",
    DEFAULT_WIDTH, DEFAULT_HEIGHT)
expect(output.error).to_equal("")
expect(output.web_pixels.len()).to_be_greater_than(0)
expect(output.engine_pixels.len()).to_be_greater_than(0)
```

</details>

#### renders demo_basics.ui.sdn through both pipelines

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = render_both_pipelines(
    "examples/06_io/ui/demo_basics.ui.sdn", "glass_dark",
    DEFAULT_WIDTH, DEFAULT_HEIGHT)
expect(output.error).to_equal("")
expect(output.web_pixels.len()).to_be_greater_than(0)
expect(output.engine_pixels.len()).to_be_greater_than(0)
```

</details>

#### pixel buffers have correct size

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = render_both_pipelines(
    "examples/06_io/ui/minimal.ui.sdn", "glass_dark",
    DEFAULT_WIDTH, DEFAULT_HEIGHT)
val expected_len = DEFAULT_WIDTH * DEFAULT_HEIGHT
expect(output.web_pixels.len().to_i32()).to_equal(expected_len)
expect(output.engine_pixels.len().to_i32()).to_equal(expected_len)
```

</details>

### Glass pixel comparison — per-channel bit-field diff

#### compares R/G/B/A channels independently

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = render_both_pipelines(
    "examples/06_io/ui/minimal.ui.sdn", "glass_dark",
    DEFAULT_WIDTH, DEFAULT_HEIGHT)
expect(output.error).to_equal("")

val channels = compare_per_channel(
    output.web_pixels, output.engine_pixels,
    DEFAULT_WIDTH, DEFAULT_HEIGHT, DEFAULT_THRESHOLD)

expect(channels.len().to_i32()).to_equal(4)
expect(channels[0].channel).to_equal("R")
expect(channels[1].channel).to_equal("G")
expect(channels[2].channel).to_equal("B")
expect(channels[3].channel).to_equal("A")

# Each channel reports valid percentages (0-10000)
for ch in channels:
    expect(ch.match_pct).to_be_greater_than(-1)
```

</details>

#### overall comparison matches pixel buffer sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = render_both_pipelines(
    "examples/06_io/ui/minimal.ui.sdn", "glass_dark",
    DEFAULT_WIDTH, DEFAULT_HEIGHT)
val result = compare_pixel_buffers(
    output.web_pixels, output.engine_pixels,
    DEFAULT_WIDTH, DEFAULT_HEIGHT, DEFAULT_THRESHOLD)
val expected_total = DEFAULT_WIDTH.to_i64() * DEFAULT_HEIGHT.to_i64()
expect(result.total_pixels).to_equal(expected_total)
```

</details>

#### generates diff image without crashing

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = render_both_pipelines(
    "examples/06_io/ui/minimal.ui.sdn", "glass_dark",
    DEFAULT_WIDTH, DEFAULT_HEIGHT)
val diff_img = generate_diff_image(
    output.web_pixels, output.engine_pixels,
    DEFAULT_WIDTH, DEFAULT_HEIGHT)
val expected_len = DEFAULT_WIDTH * DEFAULT_HEIGHT
expect(diff_img.len().to_i32()).to_equal(expected_len)
```

</details>

### Glass pixel comparison — CSS feature gap detection

#### detects backdrop-filter in glass CSS

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = render_web_pipeline_only(
    "examples/06_io/ui/demo_basics.ui.sdn", "glass_dark",
    DEFAULT_WIDTH, DEFAULT_HEIGHT)
val missing = identify_missing_features(output.web_html)
expect(missing).to_contain("backdrop-filter: blur()")
```

</details>

#### detects box-shadow in glass CSS

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = render_web_pipeline_only(
    "examples/06_io/ui/demo_basics.ui.sdn", "glass_dark",
    DEFAULT_WIDTH, DEFAULT_HEIGHT)
val missing = identify_missing_features(output.web_html)
expect(missing).to_contain("box-shadow (multi-layer)")
```

</details>

#### detects linear-gradient in glass CSS

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = render_web_pipeline_only(
    "examples/06_io/ui/demo_basics.ui.sdn", "glass_dark",
    DEFAULT_WIDTH, DEFAULT_HEIGHT)
val missing = identify_missing_features(output.web_html)
expect(missing).to_contain("linear-gradient()")
```

</details>

### Glass pixel comparison — core demo suite

<details>
<summary>Advanced: runs core glass comparison (3 demos × 2 themes)</summary>

#### runs core glass comparison (3 demos × 2 themes) _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = run_core_glass_comparison()
expect(report.total_demos).to_equal(6)
# Baseline: all demos should run without error
for r in report.results:
    expect(r.error).to_equal("")
```

</details>


</details>

<details>
<summary>Advanced: generates markdown report</summary>

#### generates markdown report _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = run_core_glass_comparison()
val md = glass_report_to_markdown(report)
expect(md.len()).to_be_greater_than(100)
expect(md).to_contain("Glass Pipeline Comparison Report")
expect(md).to_contain("Per-Demo Results")
```

</details>


</details>

### Glass pixel comparison — theme variants

#### glass_dark and glass_light produce different pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dark = render_engine_pipeline_only(
    "examples/06_io/ui/minimal.ui.sdn", "glass_dark",
    DEFAULT_WIDTH, DEFAULT_HEIGHT)
val light = render_engine_pipeline_only(
    "examples/06_io/ui/minimal.ui.sdn", "glass_light",
    DEFAULT_WIDTH, DEFAULT_HEIGHT)
expect(dark.error).to_equal("")
expect(light.error).to_equal("")

# They should differ (different background/text colors)
val result = compare_pixel_buffers(
    dark.engine_pixels, light.engine_pixels,
    DEFAULT_WIDTH, DEFAULT_HEIGHT, 0)
# Not identical
expect(result.different_pixels).to_be_greater_than(0)
```

</details>

### Glass pixel comparison — full suite

<details>
<summary>Advanced: runs full demo catalog dark-theme lane and produces complete report</summary>

#### runs full demo catalog dark-theme lane and produces complete report _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val demos = list_glass_demos_dark_only()
val report = run_glass_comparison(demos, DEFAULT_WIDTH, DEFAULT_HEIGHT)
val md = glass_report_to_markdown(report)
expect(report.total_demos).to_equal(demos.len().to_i32())
expect(md).to_contain("Glass Pipeline Comparison Report")

# All demos should parse and render without error
for r in report.results:
    expect(r.error).to_equal("")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/glass_pixel_compare_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Glass pixel comparison — single demo
- Glass pixel comparison — per-channel bit-field diff
- Glass pixel comparison — CSS feature gap detection
- Glass pixel comparison — core demo suite
- Glass pixel comparison — theme variants
- Glass pixel comparison — full suite

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 3 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
