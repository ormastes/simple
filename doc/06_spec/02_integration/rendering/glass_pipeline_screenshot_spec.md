# Glass Pipeline Screenshot Specification

> <details>

<!-- sdn-diagram:id=glass_pipeline_screenshot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=glass_pipeline_screenshot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

glass_pipeline_screenshot_spec -> std
glass_pipeline_screenshot_spec -> os
glass_pipeline_screenshot_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=glass_pipeline_screenshot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Glass Pipeline Screenshot Specification

## Scenarios

### Glass Pipeline Screenshot Comparison

#### glass test page cross-backend

#### glass_dark software vs software_rasterizer produce pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = generate_glass_test_html("glass_dark")
val sw = capture_with_backend(html, W, H, "software")
expect(sw.success).to_equal(true)
expect(sw.pixels.len()).to_equal(W * H)
# Verify non-empty (not all black)
var non_black = 0
var i = 0
while i < sw.pixels.len() and i < 1000:
    if sw.pixels[i] != 0xFF000000:
        non_black = non_black + 1
    i = i + 1
expect(non_black).to_be_greater_than(0)
```

</details>

#### glass_light renders non-empty pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = generate_glass_test_html("glass_light")
val sw = capture_with_backend(html, W, H, "software")
expect(sw.success).to_equal(true)
expect(sw.pixels.len()).to_equal(W * H)
```

</details>

#### core demos web vs engine pipeline

#### renders both pipelines for a demo

1. print comparison report


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Use a minimal demo if available
val demos = list_core_glass_demos()
if demos.len() > 0:
    val demo = demos[0]
    val output = render_both_pipelines(demo.path, "glass_dark", W, H)
    if output.error == "":
        expect(output.web_pixels.len()).to_be_greater_than(0)
        expect(output.engine_pixels.len()).to_be_greater_than(0)
        val result = compare_pixel_buffers(
            output.web_pixels, output.engine_pixels, W, H, THRESHOLD_PIPELINE)
        expect(result.match_percentage).to_be_greater_than(MIN_PCT_PIPELINE - 1)
        if result.match_percentage < 10000:
            print "Pipeline comparison for {demo.path}:"
            print_comparison_report(result)
```

</details>

#### cross-backend rendering consistency

#### software backend produces same pixels on repeated renders

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = generate_glass_test_html("glass_dark")
val first = capture_with_backend(html, W, H, "software")
val second = capture_with_backend(html, W, H, "software")
expect(first.success).to_equal(true)
expect(second.success).to_equal(true)
# Repeated renders must be deterministic
val result = compare_pixel_buffers(first.pixels, second.pixels, W, H, 0)
expect(result.match_percentage).to_equal(10000)
```

</details>

#### software vs cuda for glass_dark if cuda available

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backends = Engine2D.list_backends()
var has_cuda = false
for b in backends:
    if b == "cuda":
        has_cuda = true
if not has_cuda:
    return
val html = generate_glass_test_html("glass_dark")
val sw = capture_with_backend(html, W, H, "software")
val cuda = capture_with_backend(html, W, H, "cuda")
expect(sw.success).to_equal(true)
expect(cuda.success).to_equal(true)
val result = compare_pixel_buffers(sw.pixels, cuda.pixels, W, H, THRESHOLD_GPU)
expect(result.match_percentage).to_be_greater_than(MIN_PCT_GPU - 1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/glass_pipeline_screenshot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Glass Pipeline Screenshot Comparison

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
