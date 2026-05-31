# Screenshot Compare Profile Specification

## Scenarios

### ScreenshotCompare — compare_with_profile

#### identical buffers

#### AC-4: identical buffers with strict profile return 100% match

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
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
val profile = profile_strict()
val result = compare_with_profile(a, b, W, H, profile)
expect(result.match_percentage).to_equal(10000)
```

</details>

#### AC-4: identical buffers with wm_default profile return 100% match

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [WHITE, WHITE, WHITE, WHITE,
         WHITE, WHITE, WHITE, WHITE,
         WHITE, WHITE, WHITE, WHITE,
         WHITE, WHITE, WHITE, WHITE]
val b = [WHITE, WHITE, WHITE, WHITE,
         WHITE, WHITE, WHITE, WHITE,
         WHITE, WHITE, WHITE, WHITE,
         WHITE, WHITE, WHITE, WHITE]
val profile = profile_wm_default()
val result = compare_with_profile(a, b, W, H, profile)
expect(result.match_percentage).to_equal(10000)
```

</details>

#### AC-4: exact comparison treats alpha differences as mismatches

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [0x00000000, 0x00000000, 0x00000000, 0x00000000,
         0x00000000, 0x00000000, 0x00000000, 0x00000000,
         0x00000000, 0x00000000, 0x00000000, 0x00000000,
         0x00000000, 0x00000000, 0x00000000, 0x00000000]
val b = [0xFF000000, 0xFF000000, 0xFF000000, 0xFF000000,
         0xFF000000, 0xFF000000, 0xFF000000, 0xFF000000,
         0xFF000000, 0xFF000000, 0xFF000000, 0xFF000000,
         0xFF000000, 0xFF000000, 0xFF000000, 0xFF000000]
val result = compare_pixel_buffers(a, b, W, H, 0)
expect(result.match_percentage).to_be_less_than(10000)
```

</details>

#### large exact comparison scans beyond sentinel pixels

1. a push

2. b push
   - Expected: result.exact_match is false
   - Expected: result.different_pixels equals `1`
   - Expected: result.passed is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a: [u32] = []
var b: [u32] = []
var i = 0
while i < 10101:
    a.push(BLACK)
    b.push(BLACK)
    i = i + 1
b[7] = WHITE
val result = compare_pixel_buffers(a, b, 10101, 1, 0)
expect(result.exact_match).to_equal(false)
expect(result.different_pixels).to_equal(1)
expect(result.passed).to_equal(false)
```

</details>

#### slightly different buffers

#### AC-4: strict profile detects small differences

<details>
<summary>Executable SPipe</summary>

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
val profile = profile_strict()
val result = compare_with_profile(a, b, W, H, profile)
expect(result.match_percentage).to_be_less_than(10000)
```

</details>

#### AC-4: text_tolerant profile is more lenient than strict for same diff

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
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
val strict_result = compare_with_profile(a, b, W, H, profile_strict())
val tolerant_result = compare_with_profile(a, b, W, H, profile_text_tolerant())
val more_lenient = tolerant_result.match_percentage >= strict_result.match_percentage
expect(more_lenient).to_equal(true)
expect(tolerant_result.passed).to_equal(false)
```

</details>

#### AC-4: glass_blur profile is more lenient than strict for same diff

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
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
val strict_result = compare_with_profile(a, b, W, H, profile_strict())
val glass_result = compare_with_profile(a, b, W, H, profile_glass_blur())
val more_lenient = glass_result.match_percentage >= strict_result.match_percentage
expect(more_lenient).to_equal(true)
expect(glass_result.passed).to_equal(false)
```

</details>

#### hardening policy does not accept non-exact pixels through wm_default

<details>
<summary>Executable SPipe</summary>

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
val result = compare_with_profile(a, b, W, H, profile_wm_default())
expect(result.exact_match).to_equal(false)
expect(result.passed).to_equal(false)
```

</details>

#### completely different buffers

#### AC-4: black vs white with any profile reports low match

<details>
<summary>Executable SPipe</summary>

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
val profile = profile_wm_default()
val result = compare_with_profile(a, b, W, H, profile)
expect(result.match_percentage).to_be_less_than(5000)
```

</details>

### ScreenshotCompare — compare_with_profile result

#### ComparisonResult fields

#### AC-4: result has max_channel_diff field

<details>
<summary>Executable SPipe</summary>

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
val profile = profile_strict()
val result = compare_with_profile(a, b, W, H, profile)
expect(result.max_channel_diff).to_be_greater_than(0)
```

</details>

#### AC-4: result has total_channel_diff field

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [BLACK, BLACK, BLACK, BLACK,
         BLACK, BLACK, BLACK, BLACK,
         BLACK, BLACK, BLACK, BLACK,
         BLACK, BLACK, BLACK, BLACK]
val b = [GRAY_128, GRAY_128, GRAY_128, GRAY_128,
         GRAY_128, GRAY_128, GRAY_128, GRAY_128,
         GRAY_128, GRAY_128, GRAY_128, GRAY_128,
         GRAY_128, GRAY_128, GRAY_128, GRAY_128]
val profile = profile_strict()
val result = compare_with_profile(a, b, W, H, profile)
expect(result.total_channel_diff).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/compositor/screenshot_compare_profile_spec.spl` |
| Updated | 2026-05-31 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ScreenshotCompare — compare_with_profile
- ScreenshotCompare — compare_with_profile result

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

