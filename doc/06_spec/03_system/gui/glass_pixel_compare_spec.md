# Glass Pixel Compare Specification

> Tests covering Glass pixel comparison — single demo, Glass pixel comparison — per-channel bit-field diff, Glass pixel comparison — CSS feature gap detection, Glass pixel comparison — core demo suite, Glass pixel comparison — theme variants, Glass pixel comparison — full suite.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Glass Pixel Compare Specification

## Scenarios

### Glass pixel comparison — single demo

#### renders minimal.ui.sdn through both pipelines without error

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders minimal.ui.sdn through both pipelines without error
   - Expected: output.error equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders minimal.ui.sdn through both pipelines without error")
val output = render_both_pipelines(
    "examples/06_io/ui/minimal.ui.sdn", "glass_dark",
    DEFAULT_WIDTH, DEFAULT_HEIGHT)
expect(output.error).to_equal("")
expect(output.web_pixels.len()).to_be_greater_than(0)
expect(output.engine_pixels.len()).to_be_greater_than(0)
```

</details>

#### renders demo_basics.ui.sdn through both pipelines

- renders demo_basics.ui.sdn through both pipelines
   - Expected: output.error equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders demo_basics.ui.sdn through both pipelines")
val output = render_both_pipelines(
    "examples/06_io/ui/demo_basics.ui.sdn", "glass_dark",
    DEFAULT_WIDTH, DEFAULT_HEIGHT)
expect(output.error).to_equal("")
expect(output.web_pixels.len()).to_be_greater_than(0)
expect(output.engine_pixels.len()).to_be_greater_than(0)
```

</details>

#### pixel buffers have correct size

- pixel buffers have correct size
   - Expected: output.web_pixels.len().to_i32() equals `expected_len`
   - Expected: output.engine_pixels.len().to_i32() equals `expected_len`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pixel buffers have correct size")
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

- compares R/G/B/A channels independently
   - Expected: output.error equals ``
   - Expected: channels.len().to_i32() equals `4`
   - Expected: channels[0].channel equals `R`
   - Expected: channels[1].channel equals `G`
   - Expected: channels[2].channel equals `B`
   - Expected: channels[3].channel equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compares R/G/B/A channels independently")
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

- overall comparison matches pixel buffer sizes
   - Expected: result.total_pixels equals `expected_total`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("overall comparison matches pixel buffer sizes")
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

- generates diff image without crashing
   - Expected: diff_img.len().to_i32() equals `expected_len`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates diff image without crashing")
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

- detects backdrop-filter in glass CSS


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects backdrop-filter in glass CSS")
val output = render_web_pipeline_only(
    "examples/06_io/ui/demo_basics.ui.sdn", "glass_dark",
    DEFAULT_WIDTH, DEFAULT_HEIGHT)
val missing = identify_missing_features(output.web_html)
expect(missing).to_contain("backdrop-filter: blur()")
```

</details>

#### detects box-shadow in glass CSS

- detects box-shadow in glass CSS


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects box-shadow in glass CSS")
val output = render_web_pipeline_only(
    "examples/06_io/ui/demo_basics.ui.sdn", "glass_dark",
    DEFAULT_WIDTH, DEFAULT_HEIGHT)
val missing = identify_missing_features(output.web_html)
expect(missing).to_contain("box-shadow (multi-layer)")
```

</details>

#### detects linear-gradient in glass CSS

- detects linear-gradient in glass CSS


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects linear-gradient in glass CSS")
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

- runs core glass comparison (3 demos × 2 themes)
   - Expected: report.total_demos equals `6`
   - Expected: r.error equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs core glass comparison (3 demos × 2 themes)")
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

- generates markdown report


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates markdown report")
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

- glass_dark and glass_light produce different pixels
   - Expected: dark.error equals ``
   - Expected: light.error equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("glass_dark and glass_light produce different pixels")
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

- runs full demo catalog dark-theme lane and produces complete report
   - Expected: report.total_demos equals `demos.len().to_i32()`
   - Expected: r.error equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs full demo catalog dark-theme lane and produces complete report")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Glass pixel comparison — single demo, Glass pixel comparison — per-channel bit-field diff, Glass pixel comparison — CSS feature gap detection, Glass pixel comparison — core demo suite, Glass pixel comparison — theme variants, Glass pixel comparison — full suite.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `92791f29a2b18b1e5e0d61e51736b3f73d9a73078201c8835d21338d35a1d16a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `92791f29a2b18b1e5e0d61e51736b3f73d9a73078201c8835d21338d35a1d16a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `92791f29a2b18b1e5e0d61e51736b3f73d9a73078201c8835d21338d35a1d16a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/gui/glass_pixel_compare_spec.spl
mirror: doc/06_spec/03_system/gui/glass_pixel_compare_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/glass_pixel_compare_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/glass_pixel_compare_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/glass_pixel_compare_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/glass_pixel_compare_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders minimal.ui.sdn through both pipelines without error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/glass_pixel_compare_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders demo_basics.ui.sdn through both pipelines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/glass_pixel_compare_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pixel buffers have correct size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
