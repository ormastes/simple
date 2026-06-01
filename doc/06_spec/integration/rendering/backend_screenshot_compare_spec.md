# Backend Screenshot Compare Specification

## Scenarios

### Backend Screenshot Comparison

#### Software vs CPU deterministic buffers

#### compares glass_dark exactly

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sw = capture_fixture_backend("software", "glass_dark")
val cpu = capture_fixture_backend("cpu", "glass_dark")
expect(sw.success).to_equal(true)
expect(cpu.success).to_equal(true)
val result = compare_exact(sw.pixels, cpu.pixels, W, H)
expect(result.match_percentage).to_equal(MIN_IDENTICAL)
expect(result.passed).to_equal(true)
```

</details>

#### compares glass_light exactly

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sw = capture_fixture_backend("software", "glass_light")
val cpu = capture_fixture_backend("cpu", "glass_light")
expect(sw.success).to_equal(true)
expect(cpu.success).to_equal(true)
val result = compare_exact(sw.pixels, cpu.pixels, W, H)
expect(result.match_percentage).to_equal(MIN_IDENTICAL)
expect(result.passed).to_equal(true)
```

</details>

#### Thresholded backend-like buffers

#### keeps near-channel differences within GPU tolerance

1. pixels:  near buffer
   - Expected: result.exact_match is false
   - Expected: result.passed is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sw = capture_fixture_backend("software", "stress")
val gpu_cap = BackendCapture(
    backend_name: "gpu_like",
    pixels: _near_buffer(0xFF2563EBu32, 0xFF2765EDu32, W * H),
    success: true,
    error: ""
)
val result = compare_pixel_buffers(sw.pixels, gpu_cap.pixels, W, H, THRESHOLD_GPU)
expect(result.match_percentage).to_be_greater_than(MIN_GPU - 1)
expect(result.exact_match).to_equal(false)
expect(result.passed).to_equal(true)
```

</details>

#### reports buffer size mismatches as failed comparisons

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _solid_buffer(0xFF000000u32, W * H)
val b = _solid_buffer(0xFF000000u32, (W * H) - 1)
val result = compare_pixel_buffers(a, b, W, H, THRESHOLD_GPU)
expect(result.passed).to_equal(false)
expect(result.match_percentage).to_equal(0)
```

</details>

#### reports invalid dimensions as failed comparisons

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compare_pixel_buffers([], [], 0, H, THRESHOLD_GPU)
expect(result.exact_match).to_equal(false)
expect(result.passed).to_equal(false)
expect(result.match_percentage).to_equal(0)
```

</details>

#### keeps invalid dimensions failed through profile comparison

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compare_with_profile([], [], 0, H, profile_strict())
expect(result.exact_match).to_equal(false)
expect(result.passed).to_equal(false)
expect(result.match_percentage).to_equal(0)
```

</details>

#### Diff image generation

#### produces all-green for identical buffers

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size = 10 * 10
val buf_a = _solid_buffer(0xFF336699u32, size)
val buf_b = _solid_buffer(0xFF336699u32, size)
val diff = generate_diff_image(buf_a, buf_b, 10, 10)
expect(diff.len()).to_equal(size)
val first = diff[0]
val green = ((first >> 8) & 0xFF).to_i32()
val red = ((first >> 16) & 0xFF).to_i32()
expect(green).to_be_greater_than(red)
```

</details>

#### produces red pixels for differing regions

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf_a = _solid_buffer(0xFF000000u32, 100)
val buf_b = _solid_buffer(0xFFFFFFFFu32, 100)
val diff = generate_diff_image(buf_a, buf_b, 10, 10)
val first = diff[0]
val red = ((first >> 16) & 0xFF).to_i32()
expect(red).to_be_greater_than(100)
```

</details>

#### keeps viewport-sized diagnostics for truncated buffers

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf_a = _solid_buffer(0xFF000000u32, 100)
val buf_b = _solid_buffer(0xFF000000u32, 99)
val diff = generate_diff_image(buf_a, buf_b, 10, 10)
expect(diff.len()).to_equal(100)
val last = diff[99]
val red = ((last >> 16) & 0xFF).to_i32()
val green = ((last >> 8) & 0xFF).to_i32()
expect(red).to_be_greater_than(green)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/rendering/backend_screenshot_compare_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Backend Screenshot Comparison

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

