# Effect Engine Compare Specification

> 1. print comparison report

<!-- sdn-diagram:id=effect_engine_compare_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=effect_engine_compare_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

effect_engine_compare_spec -> std
effect_engine_compare_spec -> os
effect_engine_compare_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=effect_engine_compare_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Effect Engine Compare Specification

## Scenarios

### Effect Engine Comparison (Int32 vs Float64)

#### full scene comparison

#### glass_dark renders within effect engine tolerance

1. print comparison report


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = generate_glass_test_html("glass_dark")
val int_cap = capture_with_effect_engine(html, W, H, "int")
val float_cap = capture_with_effect_engine(html, W, H, "float")
expect(int_cap.success).to_equal(true)
expect(float_cap.success).to_equal(true)
val result = compare_pixel_buffers(int_cap.pixels, float_cap.pixels, W, H, THRESHOLD_EE)
expect(result.match_percentage).to_be_greater_than(MIN_PCT_EE - 1)
if result.match_percentage < 10000:
    print "Int32 vs Float64 on glass_dark:"
    print_comparison_report(result)
```

</details>

#### glass_light renders within effect engine tolerance

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = generate_glass_test_html("glass_light")
val int_cap = capture_with_effect_engine(html, W, H, "int")
val float_cap = capture_with_effect_engine(html, W, H, "float")
expect(int_cap.success).to_equal(true)
expect(float_cap.success).to_equal(true)
val result = compare_pixel_buffers(int_cap.pixels, float_cap.pixels, W, H, THRESHOLD_EE)
expect(result.match_percentage).to_be_greater_than(MIN_PCT_EE - 1)
```

</details>

<details>
<summary>Advanced: stress test renders within effect engine tolerance</summary>

#### stress test renders within effect engine tolerance

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = build_rendering_stress_html()
val int_cap = capture_with_effect_engine(html, W, H, "int")
val float_cap = capture_with_effect_engine(html, W, H, "float")
expect(int_cap.success).to_equal(true)
expect(float_cap.success).to_equal(true)
val result = compare_pixel_buffers(int_cap.pixels, float_cap.pixels, W, H, THRESHOLD_EE)
expect(result.match_percentage).to_be_greater_than(MIN_PCT_EE - 1)
```

</details>


</details>

#### per-channel analysis

#### glass_dark per-channel diff within tolerance

1. print channel report


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = generate_glass_test_html("glass_dark")
val int_cap = capture_with_effect_engine(html, W, H, "int")
val float_cap = capture_with_effect_engine(html, W, H, "float")
expect(int_cap.success).to_equal(true)
expect(float_cap.success).to_equal(true)
val channels = compare_per_channel(int_cap.pixels, float_cap.pixels, W, H, THRESHOLD_EE)
print_channel_report(channels)
# Each channel should be within tolerance
for ch in channels:
    expect(ch.match_pct).to_be_greater_than(MIN_PCT_EE - 1)
```

</details>

#### pixel buffer sizes match

#### int and float engines produce same buffer size

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = generate_glass_test_html("glass_dark")
val int_cap = capture_with_effect_engine(html, W, H, "int")
val float_cap = capture_with_effect_engine(html, W, H, "float")
expect(int_cap.success).to_equal(true)
expect(float_cap.success).to_equal(true)
expect(int_cap.pixels.len()).to_equal(float_cap.pixels.len())
expect(int_cap.pixels.len()).to_equal(W * H)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/effect_engine_compare_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Effect Engine Comparison (Int32 vs Float64)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
