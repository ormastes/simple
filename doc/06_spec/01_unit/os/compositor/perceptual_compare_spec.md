# Perceptual Compare Specification

> <details>

<!-- sdn-diagram:id=perceptual_compare_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=perceptual_compare_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

perceptual_compare_spec -> std
perceptual_compare_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=perceptual_compare_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Perceptual Compare Specification

## Scenarios

### PerceptualCompare — yiq_distance

#### identical pixels

#### AC-4: returns zero distance for identical black pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dist = yiq_distance(BLACK, BLACK)
expect(dist).to_equal(0.0)
```

</details>

#### AC-4: returns zero distance for identical white pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dist = yiq_distance(WHITE, WHITE)
expect(dist).to_equal(0.0)
```

</details>

#### AC-4: returns zero distance for identical color pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dist = yiq_distance(RED, RED)
expect(dist).to_equal(0.0)
```

</details>

#### maximally different pixels

#### AC-4: returns large distance for black vs white

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dist = yiq_distance(BLACK, WHITE)
expect(dist).to_be_greater_than(0.5)
```

</details>

#### perceptually similar pixels

#### AC-4: returns small distance for nearby grays

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dist = yiq_distance(GRAY_128, GRAY_192)
expect(dist).to_be_less_than(0.5)
```

</details>

#### color channel differences

#### AC-4: red vs green has nonzero distance

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dist = yiq_distance(RED, GREEN)
expect(dist).to_be_greater_than(0.0)
```

</details>

#### AC-4: red vs blue has nonzero distance

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dist = yiq_distance(RED, BLUE)
expect(dist).to_be_greater_than(0.0)
```

</details>

### PerceptualCompare — is_antialiased

#### uniform region

#### AC-4: pixel in uniform solid block is not antialiased

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 4x4 all-black image
val pixels = [BLACK, BLACK, BLACK, BLACK,
              BLACK, BLACK, BLACK, BLACK,
              BLACK, BLACK, BLACK, BLACK,
              BLACK, BLACK, BLACK, BLACK]
val result = is_antialiased(pixels, 1, 1, W, H)
expect(result).to_equal(false)
```

</details>

#### sharp edge

#### AC-4: pixel at a hard black/white boundary is not antialiased

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Left half black, right half white — hard edge at column 2
val pixels = [BLACK, BLACK, WHITE, WHITE,
              BLACK, BLACK, WHITE, WHITE,
              BLACK, BLACK, WHITE, WHITE,
              BLACK, BLACK, WHITE, WHITE]
val result = is_antialiased(pixels, 1, 1, W, H)
expect(result).to_equal(false)
```

</details>

#### anti-aliased edge

#### AC-4: pixel with intermediate gray neighbors along edge is detected as AA

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Row pattern: BLACK, GRAY, WHITE — gray is AA between black and white
val pixels = [BLACK, BLACK,    WHITE,    WHITE,
              BLACK, GRAY_64,  GRAY_192, WHITE,
              BLACK, GRAY_128, GRAY_192, WHITE,
              BLACK, BLACK,    WHITE,    WHITE]
val result = is_antialiased(pixels, 1, 1, W, H)
expect(result).to_equal(true)
```

</details>

#### corner pixels

#### AC-4: corner pixel (0,0) does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = [WHITE, BLACK, BLACK, BLACK,
              BLACK, BLACK, BLACK, BLACK,
              BLACK, BLACK, BLACK, BLACK,
              BLACK, BLACK, BLACK, BLACK]
val result = is_antialiased(pixels, 0, 0, W, H)
# Corner with fewer neighbors — should not crash
expect(result).to_equal(false)
```

</details>

### PerceptualCompare — compare_perceptual

#### identical buffers

#### AC-4: identical buffers yield 100% match and zero mismatches

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [BLACK, BLACK, BLACK, BLACK,
         BLACK, BLACK, BLACK, BLACK,
         BLACK, BLACK, BLACK, BLACK,
         BLACK, BLACK, BLACK, BLACK]
val b = [BLACK, BLACK, BLACK, BLACK,
         BLACK, BLACK, BLACK, BLACK,
         BLACK, BLACK, BLACK, BLACK,
         BLACK, BLACK, BLACK, BLACK]
val result = compare_perceptual(a, b, W, H, 0.1, true)
expect(result.mismatched_pixels).to_equal(0)
expect(result.total_pixels).to_equal(16)
expect(result.match_percentage).to_equal(10000)
```

</details>

#### completely different buffers

#### AC-4: all-black vs all-white yields zero or near-zero match

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [BLACK, BLACK, BLACK, BLACK,
         BLACK, BLACK, BLACK, BLACK,
         BLACK, BLACK, BLACK, BLACK,
         BLACK, BLACK, BLACK, BLACK]
val b = [WHITE, WHITE, WHITE, WHITE,
         WHITE, WHITE, WHITE, WHITE,
         WHITE, WHITE, WHITE, WHITE,
         WHITE, WHITE, WHITE, WHITE]
val result = compare_perceptual(a, b, W, H, 0.1, true)
expect(result.mismatched_pixels).to_equal(16)
expect(result.match_percentage).to_equal(0)
```

</details>

#### threshold sensitivity

#### AC-4: high threshold makes near-similar pixels match

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [GRAY_128, GRAY_128, GRAY_128, GRAY_128,
         GRAY_128, GRAY_128, GRAY_128, GRAY_128,
         GRAY_128, GRAY_128, GRAY_128, GRAY_128,
         GRAY_128, GRAY_128, GRAY_128, GRAY_128]
val b = [GRAY_192, GRAY_192, GRAY_192, GRAY_192,
         GRAY_192, GRAY_192, GRAY_192, GRAY_192,
         GRAY_192, GRAY_192, GRAY_192, GRAY_192,
         GRAY_192, GRAY_192, GRAY_192, GRAY_192]
# Very high threshold — should match despite difference
val result = compare_perceptual(a, b, W, H, 1.0, true)
expect(result.mismatched_pixels).to_equal(0)
```

</details>

#### AC-4: zero threshold makes any difference a mismatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [GRAY_128, GRAY_128, GRAY_128, GRAY_128,
         GRAY_128, GRAY_128, GRAY_128, GRAY_128,
         GRAY_128, GRAY_128, GRAY_128, GRAY_128,
         GRAY_128, GRAY_128, GRAY_128, GRAY_128]
val b = [GRAY_192, GRAY_192, GRAY_192, GRAY_192,
         GRAY_192, GRAY_192, GRAY_192, GRAY_192,
         GRAY_192, GRAY_192, GRAY_192, GRAY_192,
         GRAY_192, GRAY_192, GRAY_192, GRAY_192]
val result = compare_perceptual(a, b, W, H, 0.0, true)
expect(result.mismatched_pixels).to_be_greater_than(0)
```

</details>

#### AA exclusion

#### AC-4: include_aa=false excludes AA pixels from mismatch count

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Craft image with an AA edge
val a = [BLACK, BLACK,    WHITE,    WHITE,
         BLACK, GRAY_64,  GRAY_192, WHITE,
         BLACK, GRAY_128, GRAY_192, WHITE,
         BLACK, BLACK,    WHITE,    WHITE]
val b = [BLACK, BLACK,    WHITE,    WHITE,
         BLACK, GRAY_128, GRAY_128, WHITE,
         BLACK, GRAY_192, GRAY_128, WHITE,
         BLACK, BLACK,    WHITE,    WHITE]
val with_aa = compare_perceptual(a, b, W, H, 0.1, true)
val without_aa = compare_perceptual(a, b, W, H, 0.1, false)
# Excluding AA should report fewer mismatches (or equal)
val fewer_or_equal = without_aa.mismatched_pixels <= with_aa.mismatched_pixels
expect(fewer_or_equal).to_equal(true)
```

</details>

#### AC-4: aa_pixels count is reported in result

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [BLACK, GRAY_128, WHITE, WHITE,
         BLACK, GRAY_128, WHITE, WHITE,
         BLACK, GRAY_128, WHITE, WHITE,
         BLACK, GRAY_128, WHITE, WHITE]
val b = [BLACK, GRAY_64,  WHITE, WHITE,
         BLACK, GRAY_64,  WHITE, WHITE,
         BLACK, GRAY_64,  WHITE, WHITE,
         BLACK, GRAY_64,  WHITE, WHITE]
val result = compare_perceptual(a, b, W, H, 0.1, false)
# aa_pixels should be non-negative
val non_neg = result.aa_pixels >= 0
expect(non_neg).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/perceptual_compare_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PerceptualCompare — yiq_distance
- PerceptualCompare — is_antialiased
- PerceptualCompare — compare_perceptual

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
