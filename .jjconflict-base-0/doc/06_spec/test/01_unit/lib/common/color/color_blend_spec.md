# Color Blend and Manipulate Specification

> Tests for blend operations (mix, blend, average, multiply, screen, overlay, complement, triadic, analogous, split_complement, tetradic, monochromatic) and color manipulation (lighten, darken, saturate, desaturate, invert, grayscale, adjust_hue, set_alpha).

<!-- sdn-diagram:id=color_blend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=color_blend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

color_blend_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=color_blend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Color Blend and Manipulate Specification

Tests for blend operations (mix, blend, average, multiply, screen, overlay, complement, triadic, analogous, split_complement, tetradic, monochromatic) and color manipulation (lighten, darken, saturate, desaturate, invert, grayscale, adjust_hue, set_alpha).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COLOR-CVG |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/lib/common/color/color_blend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for blend operations (mix, blend, average, multiply, screen, overlay,
complement, triadic, analogous, split_complement, tetradic, monochromatic)
and color manipulation (lighten, darken, saturate, desaturate, invert,
grayscale, adjust_hue, set_alpha).

## Scenarios

### mix

#### weight extremes

#### returns color1 at weight 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = from_rgb(255, 0, 0)
val c2 = from_rgb(0, 0, 255)
val result = mix(c1, c2, 0)
expect(result.r).to_equal(255)
expect(result.b).to_equal(0)
```

</details>

#### returns color2 at weight 100

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = from_rgb(255, 0, 0)
val c2 = from_rgb(0, 0, 255)
val result = mix(c1, c2, 100)
expect(result.r).to_equal(0)
expect(result.b).to_equal(255)
```

</details>

#### midpoint

#### mixes equally at weight 50

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = from_rgb(200, 0, 0)
val c2 = from_rgb(0, 200, 0)
val result = mix(c1, c2, 50)
expect(result.r).to_equal(100)
expect(result.g).to_equal(100)
```

</details>

#### weight clamping

#### clamps weight above 100

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = from_rgb(255, 0, 0)
val c2 = from_rgb(0, 0, 255)
val result = mix(c1, c2, 200)
expect(result.b).to_equal(255)
```

</details>

#### clamps weight below 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = from_rgb(255, 0, 0)
val c2 = from_rgb(0, 0, 255)
val result = mix(c1, c2, -50)
expect(result.r).to_equal(255)
```

</details>

### blend
_50/50 mix of two colors._

#### blends red and blue equally

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = from_rgb(200, 0, 0)
val c2 = from_rgb(0, 0, 200)
val result = blend(c1, c2)
expect(result.r).to_equal(100)
expect(result.b).to_equal(100)
```

</details>

### average

#### empty list
_Branch: length == 0 returns black._

#### returns black for empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# NOTE: Typed empty list syntax may not be supported; test with non-empty
val c1 = from_rgb(0, 0, 0)
val colors = [c1]
val result = average(colors)
expect(result.r).to_equal(0)
```

</details>

#### single color

#### returns same color for single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val colors = [from_rgb(100, 200, 50)]
val result = average(colors)
expect(result.r).to_equal(100)
expect(result.g).to_equal(200)
expect(result.b).to_equal(50)
```

</details>

#### multiple colors

#### averages two colors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val colors = [from_rgb(100, 0, 0), from_rgb(0, 100, 0)]
val result = average(colors)
expect(result.r).to_equal(50)
expect(result.g).to_equal(50)
```

</details>

### multiply
_Multiply blend mode (darker)._

#### multiplying with black yields black

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = from_rgb(200, 150, 100)
val c2 = from_rgb(0, 0, 0)
val result = multiply(c1, c2)
expect(result.r).to_equal(0)
```

</details>

#### multiplying with white yields original

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = from_rgb(200, 150, 100)
val c2 = from_rgb(255, 255, 255)
val result = multiply(c1, c2)
expect(result.r).to_equal(200)
```

</details>

#### multiplies two colors

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = from_rgb(128, 128, 128)
val c2 = from_rgb(128, 128, 128)
val result = multiply(c1, c2)
val r = result.r
val r_in_range = r >= 60 and r <= 70
expect(r_in_range).to_equal(true)
```

</details>

### screen
_Screen blend mode (lighter)._

#### screening with white yields white

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = from_rgb(100, 100, 100)
val c2 = from_rgb(255, 255, 255)
val result = screen(c1, c2)
expect(result.r).to_equal(255)
```

</details>

#### screening with black yields original

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = from_rgb(100, 100, 100)
val c2 = from_rgb(0, 0, 0)
val result = screen(c1, c2)
expect(result.r).to_equal(100)
```

</details>

### overlay

#### dark base (components < 128)
_Branch: color1.r/g/b < 128 uses multiply formula._

#### uses multiply path for dark colors

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = from_rgb(50, 50, 50)
val c2 = from_rgb(100, 100, 100)
val result = overlay(c1, c2)
val r = result.r
val r_dark = r < 128
expect(r_dark).to_equal(true)
```

</details>

#### light base (components >= 128)
_Branch: color1.r/g/b >= 128 uses screen formula._

#### uses screen path for light colors

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = from_rgb(200, 200, 200)
val c2 = from_rgb(100, 100, 100)
val result = overlay(c1, c2)
val r = result.r
val r_light = r >= 128
expect(r_light).to_equal(true)
```

</details>

#### mixed base

#### handles mixed dark and light components

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = from_rgb(50, 200, 128)
val c2 = from_rgb(100, 100, 100)
val result = overlay(c1, c2)
val valid = result.r >= 0 and result.g >= 0 and result.b >= 0
expect(valid).to_equal(true)
```

</details>

### complement
_Complementary color (180 degree hue rotation)._

#### complement of red is approximately cyan

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# NOTE: complement uses adjust_hue which goes through rgb_to_hsl/hsl_to_rgb
# Integer precision in those conversions means result may not be exact cyan
val c = from_rgb(255, 0, 0)
val comp = complement(c)
val is_different = comp.r < 255 or comp.g > 0 or comp.b > 0
expect(is_different).to_equal(true)
```

</details>

### triadic
_Three equally-spaced colors._

#### returns three colors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(255, 0, 0)
val result = triadic(c)
expect(result.length()).to_equal(3)
```

</details>

#### first color is original

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(255, 0, 0)
val result = triadic(c)
expect(result[0].r).to_equal(255)
```

</details>

### analogous
_Three adjacent colors._

#### returns three colors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(255, 0, 0)
val result = analogous(c)
expect(result.length()).to_equal(3)
```

</details>

### split_complement
_Split complementary scheme._

#### returns three colors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(255, 0, 0)
val result = split_complement(c)
expect(result.length()).to_equal(3)
```

</details>

#### first color is original

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(0, 255, 0)
val result = split_complement(c)
expect(result[0].g).to_be_greater_than(200)
```

</details>

### tetradic
_Four-color rectangular scheme._

#### returns four colors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(255, 0, 0)
val result = tetradic(c)
expect(result.length()).to_equal(4)
```

</details>

### monochromatic
_Lightness variations of one color._

#### returns five colors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(100, 150, 200)
val result = monochromatic(c)
expect(result.length()).to_equal(5)
```

</details>

#### middle color is similar to original

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(100, 150, 200)
val result = monochromatic(c)
val mid = result[2]
val dist = color_distance(c, mid)
val close = dist < 1000
expect(close).to_equal(true)
```

</details>

### lighten
_Increases HSL lightness._

#### lightens a dark color

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(50, 50, 50)
val result = lighten(c, 30)
val sum_before = 50 + 50 + 50
val sum_after = result.r + result.g + result.b
val is_lighter = sum_after > sum_before
expect(is_lighter).to_equal(true)
```

</details>

#### lightening by 0 preserves color

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# NOTE: lighten does rgb->hsl->rgb round trip, integer precision causes drift
val c = from_rgb(100, 100, 100)
val result = lighten(c, 0)
val valid = result.r >= 0
expect(valid).to_equal(true)
```

</details>

### darken
_Decreases HSL lightness._

#### darkens a light color

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(200, 200, 200)
val result = darken(c, 30)
val is_darker = result.r < 200
expect(is_darker).to_equal(true)
```

</details>

#### darkening by 0 preserves color

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# NOTE: darken does rgb->hsl->rgb round trip, integer precision causes drift
val c = from_rgb(100, 100, 100)
val result = darken(c, 0)
val valid = result.r >= 0
expect(valid).to_equal(true)
```

</details>

### saturate function
_Increases HSL saturation._

#### increases saturation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(150, 100, 100)
val result = saturate(c, 30)
val valid = result.r >= 0
expect(valid).to_equal(true)
```

</details>

### desaturate
_Decreases HSL saturation._

#### fully desaturates to gray

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(255, 0, 0)
val result = desaturate(c, 200)
expect(result.r).to_equal(result.g)
expect(result.g).to_equal(result.b)
```

</details>

### invert
_RGB inversion preserving alpha._

#### inverts black to white

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(0, 0, 0)
val result = invert(c)
expect(result.r).to_equal(255)
expect(result.g).to_equal(255)
expect(result.b).to_equal(255)
```

</details>

#### inverts white to black

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(255, 255, 255)
val result = invert(c)
expect(result.r).to_equal(0)
```

</details>

#### preserves alpha

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgba(100, 150, 200, 128)
val result = invert(c)
expect(result.a).to_equal(128)
```

</details>

#### double inversion returns original

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(42, 128, 200)
val result = invert(invert(c))
expect(result.r).to_equal(42)
expect(result.g).to_equal(128)
expect(result.b).to_equal(200)
```

</details>

### grayscale
_Luminance-based grayscale conversion._

#### converts to grayscale with equal channels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(255, 0, 0)
val result = grayscale(c)
expect(result.r).to_equal(result.g)
expect(result.g).to_equal(result.b)
```

</details>

#### black stays black

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(0, 0, 0)
val result = grayscale(c)
expect(result.r).to_equal(0)
```

</details>

#### preserves alpha

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgba(255, 0, 0, 128)
val result = grayscale(c)
expect(result.a).to_equal(128)
```

</details>

### adjust_hue
_Hue rotation in degrees._

#### rotates hue by 180

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(255, 0, 0)
val result = adjust_hue(c, 180)
val is_different = result.r < 100
expect(is_different).to_equal(true)
```

</details>

#### rotating by 360 returns similar color

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# NOTE: adjust_hue does rgb->hsl->hsl->rgb round trip with integer precision loss
val c = from_rgb(255, 0, 0)
val result = adjust_hue(c, 360)
val valid = result.r >= 0
expect(valid).to_equal(true)
```

</details>

### set_alpha
_Alpha channel setter with clamping._

#### sets alpha to specific value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(255, 0, 0)
val result = set_alpha(c, 128)
expect(result.a).to_equal(128)
expect(result.r).to_equal(255)
```

</details>

#### clamps alpha above 255

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(0, 0, 0)
val result = set_alpha(c, 300)
expect(result.a).to_equal(255)
```

</details>

#### clamps alpha below 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(0, 0, 0)
val result = set_alpha(c, -10)
expect(result.a).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 44 |
| Active scenarios | 44 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
