# Pixel Diff Core Specification

> <details>

<!-- sdn-diagram:id=pixel_diff_core_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pixel_diff_core_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pixel_diff_core_spec -> std
pixel_diff_core_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pixel_diff_core_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pixel Diff Core Specification

## Scenarios

### per_channel_delta

#### identical pixels give delta 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _s(_bm1(100, 150, 200, 255))
val b = _s(_bm1(100, 150, 200, 255))
val d = per_channel_delta(a, b)
expect d to_equal 0
```

</details>

#### single channel differs by 50 gives delta 50

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _s(_bm1(100, 0, 0, 0))
val b = _s(_bm1(50, 0, 0, 0))
val d = per_channel_delta(a, b)
expect d to_equal 50
```

</details>

#### returns max across channels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _s(_bm1(255, 10, 0, 0))
val b = _s(_bm1(0, 0, 0, 0))
val d = per_channel_delta(a, b)
expect d to_equal 255
```

</details>

### pixel_matches

#### tolerance >= channel delta returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _s(_bm1(100, 0, 0, 0))
val b = _s(_bm1(98, 0, 0, 0))
val result = pixel_matches(a, b, 2)
expect result to_equal true
```

</details>

#### tolerance < channel delta returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _s(_bm1(100, 0, 0, 0))
val b = _s(_bm1(97, 0, 0, 0))
val result = pixel_matches(a, b, 2)
expect result to_equal false
```

</details>

### mismatch_ratio

#### identical bitmaps give ratio 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _bm1(128, 64, 32, 255)
val b = _bm1(128, 64, 32, 255)
val r = mismatch_ratio(a, b, 0)
expect r to_equal 0.0
```

</details>

#### 1-pixel differ at tolerance 0 gives ratio 1.0 for 1x1

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _bm1(128, 0, 0, 255)
val b = _bm1(127, 0, 0, 255)
val r = mismatch_ratio(a, b, 0)
expect r to_equal 1.0
```

</details>

#### dimension mismatch returns 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = BitmapRef.of(1, 1, [0, 0, 0, 255])
val b = BitmapRef.of(2, 1, [0, 0, 0, 255, 0, 0, 0, 255])
val r = mismatch_ratio(a, b, 0)
expect r to_equal 1.0
```

</details>

### max_channel_delta

#### identical bitmaps give 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _bm1(200, 100, 50, 255)
val b = _bm1(200, 100, 50, 255)
val d = max_channel_delta(a, b)
expect d to_equal 0
```

</details>

#### all-red vs all-black 2x2 gives 255

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = max_channel_delta(_red_2x2(), _black_2x2())
expect d to_equal 255
```

</details>

#### dimension mismatch returns 255

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = BitmapRef.of(1, 1, [0, 0, 0, 255])
val b = BitmapRef.of(2, 1, [0, 0, 0, 255, 0, 0, 0, 255])
val d = max_channel_delta(a, b)
expect d to_equal 255
```

</details>

### bitmap_diff_rect

#### identical bitmaps return empty rect (0,0,0,0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _red_2x2()
val b = _red_2x2()
val rect = bitmap_diff_rect(a, b, 0)
expect rect.left to_equal 0
expect rect.top to_equal 0
expect rect.right to_equal 0
expect rect.bottom to_equal 0
```

</details>

#### 2x2 with single differing pixel at (1,1) returns rect covering that pixel

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build a 2x2 bitmap: all pixels match except bottom-right (1,1)
val a = BitmapRef.of(2, 2, [
    0, 0, 0, 255,  0, 0, 0, 255,
    0, 0, 0, 255,  0, 0, 0, 255
])
val b = BitmapRef.of(2, 2, [
    0, 0, 0, 255,  0, 0, 0, 255,
    0, 0, 0, 255,  255, 0, 0, 255
])
val rect = bitmap_diff_rect(a, b, 0)
expect rect.left to_equal 1
expect rect.top to_equal 1
expect rect.right to_equal 2
expect rect.bottom to_equal 2
```

</details>

### summarize

#### populates all 4 fields correctly for a 1-pixel difference

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _bm1(255, 0, 0, 255)
val b = _bm1(0, 0, 0, 255)
val s = summarize(a, b, 0)
expect s.ratio to_equal 1.0
expect s.max_channel_delta to_equal 255
expect s.mismatched_pixels to_equal 1
expect s.diff_rect.left to_equal 0
expect s.diff_rect.top to_equal 0
expect s.diff_rect.right to_equal 1
expect s.diff_rect.bottom to_equal 1
```

</details>

#### identical bitmaps give zeroed summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _bm1(100, 100, 100, 255)
val b = _bm1(100, 100, 100, 255)
val s = summarize(a, b, 0)
expect s.ratio to_equal 0.0
expect s.max_channel_delta to_equal 0
expect s.mismatched_pixels to_equal 0
val empty = s.diff_rect.is_empty()
expect empty to_equal true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/reftest/parity/pixel_diff_core_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- per_channel_delta
- pixel_matches
- mismatch_ratio
- max_channel_delta
- bitmap_diff_rect
- summarize

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
