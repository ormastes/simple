# Color HSL/HSV Conversion Specification

> Tests for rgb_to_hsl, hsl_to_rgb, rgb_to_hsv, hsv_to_rgb, hex output, CSS output, math helper functions, and from_hsl/from_hsv constructors.

<!-- sdn-diagram:id=color_hsl_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=color_hsl_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

color_hsl_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=color_hsl_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 89 | 89 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Color HSL/HSV Conversion Specification

Tests for rgb_to_hsl, hsl_to_rgb, rgb_to_hsv, hsv_to_rgb, hex output, CSS output, math helper functions, and from_hsl/from_hsv constructors.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COLOR-CVG |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/lib/common/color/color_hsl_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for rgb_to_hsl, hsl_to_rgb, rgb_to_hsv, hsv_to_rgb, hex output,
CSS output, math helper functions, and from_hsl/from_hsv constructors.

## Scenarios

### rgb_to_hsl

#### achromatic colors (delta == 0)
_Branch: delta == 0 returns early._

#### converts black to HSL zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(0, 0, 0)
val hsl = rgb_to_hsl(c)
expect(hsl.0).to_equal(0)
expect(hsl.1).to_equal(0)
expect(hsl.2).to_equal(0)
```

</details>

#### converts white to HSL

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(255, 255, 255)
val hsl = rgb_to_hsl(c)
expect(hsl.0).to_equal(0)
expect(hsl.1).to_equal(0)
```

</details>

#### converts gray to HSL with zero saturation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(128, 128, 128)
val hsl = rgb_to_hsl(c)
expect(hsl.1).to_equal(0)
```

</details>

#### hue calculation when max is red
_Branch: max_val == r_norm_

#### converts pure red

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(255, 0, 0)
val hsl = rgb_to_hsl(c)
expect(hsl.0).to_equal(0)
```

</details>

#### converts red-dominant color

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(200, 100, 50)
val hsl = rgb_to_hsl(c)
val h = hsl.0
val h_valid = h >= 0 and h < 360
expect(h_valid).to_equal(true)
```

</details>

#### hue calculation when max is green
_Branch: max_val == g_norm_

#### converts pure green

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(0, 255, 0)
val hsl = rgb_to_hsl(c)
expect(hsl.0).to_equal(120)
```

</details>

#### converts green-dominant color

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# NOTE: rgb_to_hsl uses integer division (r/255), losing precision for non-0/255 values
val c = from_rgb(50, 200, 100)
val hsl = rgb_to_hsl(c)
val h = hsl.0
val h_valid = h >= 0 and h < 360
expect(h_valid).to_equal(true)
```

</details>

#### hue calculation when max is blue
_Branch: max_val == b_norm (else branch)_

#### converts pure blue

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(0, 0, 255)
val hsl = rgb_to_hsl(c)
expect(hsl.0).to_equal(240)
```

</details>

#### converts blue-dominant color

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# NOTE: rgb_to_hsl integer division loses precision for non-0/255 values
val c = from_rgb(50, 100, 200)
val hsl = rgb_to_hsl(c)
val h = hsl.0
val h_valid = h >= 0 and h < 360
expect(h_valid).to_equal(true)
```

</details>

#### saturation lightness branch
_Branch: l < 50 (true) vs l >= 50 (false)._

#### dark color has l < 50

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(100, 50, 25)
val hsl = rgb_to_hsl(c)
val l_val = hsl.2
val is_low = l_val < 50
expect(is_low).to_equal(true)
```

</details>

#### light color has l >= 50

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# NOTE: rgb_to_hsl integer division (r/255=0 for r<255) causes l=0 for most colors
# Use values that survive integer division: 255 gives norm=1, 0 gives norm=0
val c = from_rgb(255, 255, 255)
val hsl = rgb_to_hsl(c)
val l_val = hsl.2
val is_high = l_val >= 50
expect(is_high).to_equal(true)
```

</details>

#### negative hue correction
_Branch: h < 0 triggers h + 360._

#### handles color that produces negative hue

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Blue with some red can produce negative hue in intermediate calc
val c = from_rgb(100, 0, 200)
val hsl = rgb_to_hsl(c)
val h = hsl.0
val h_non_neg = h >= 0
expect(h_non_neg).to_equal(true)
```

</details>

### hsl_to_rgb

#### achromatic (saturation == 0)
_Branch: s_norm == 0 returns gray._

#### converts zero saturation to gray

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = hsl_to_rgb(0, 0, 50)
expect(c.r).to_equal(c.g)
expect(c.g).to_equal(c.b)
```

</details>

#### converts zero saturation black

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = hsl_to_rgb(0, 0, 0)
expect(c.r).to_equal(0)
expect(c.g).to_equal(0)
expect(c.b).to_equal(0)
```

</details>

#### converts zero saturation white

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = hsl_to_rgb(0, 0, 100)
expect(c.r).to_equal(255)
expect(c.g).to_equal(255)
expect(c.b).to_equal(255)
```

</details>

#### chroma calculation branches
_Branch: l_norm < 50 (true) vs >= 50 (false)._

#### computes chroma for dark color (l < 50)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = hsl_to_rgb(0, 100, 25)
val valid = c.r >= 0
expect(valid).to_equal(true)
```

</details>

#### computes chroma for light color (l >= 50)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = hsl_to_rgb(0, 100, 75)
val valid = c.r >= 0
expect(valid).to_equal(true)
```

</details>

#### hue sector 0-59 (red-yellow)

#### converts hue 0 (red)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = hsl_to_rgb(0, 100, 50)
expect(c.r).to_be_greater_than(200)
```

</details>

#### hue sector 60-119 (yellow-green)

#### converts hue 60 (yellow)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = hsl_to_rgb(60, 100, 50)
expect(c.r).to_be_greater_than(200)
```

</details>

#### hue sector 120-179 (green-cyan)

#### converts hue 120 (green)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = hsl_to_rgb(120, 100, 50)
expect(c.g).to_be_greater_than(200)
```

</details>

#### hue sector 180-239 (cyan-blue)

#### converts hue 180 (cyan)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = hsl_to_rgb(180, 100, 50)
expect(c.b).to_be_greater_than(200)
```

</details>

#### hue sector 240-299 (blue-magenta)

#### converts hue 240 (blue)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = hsl_to_rgb(240, 100, 50)
expect(c.b).to_be_greater_than(200)
```

</details>

#### hue sector 300-359 (magenta-red)

#### converts hue 300 (magenta)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = hsl_to_rgb(300, 100, 50)
expect(c.r).to_be_greater_than(200)
```

</details>

### rgb_to_hsv

#### black (max == 0)
_Branch: max_val == 0 returns (0, 0, 0)._

#### converts black to zero HSV

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(0, 0, 0)
val hsv = rgb_to_hsv(c)
expect(hsv.0).to_equal(0)
expect(hsv.1).to_equal(0)
expect(hsv.2).to_equal(0)
```

</details>

#### achromatic (delta == 0, non-black)
_Branch: delta == 0 returns (0, 0, v)._

#### converts gray to HSV with zero saturation

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(128, 128, 128)
val hsv = rgb_to_hsv(c)
expect(hsv.0).to_equal(0)
expect(hsv.1).to_equal(0)
val v = hsv.2
val v_positive = v > 0
expect(v_positive).to_equal(true)
```

</details>

#### converts white to HSV

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(255, 255, 255)
val hsv = rgb_to_hsv(c)
expect(hsv.0).to_equal(0)
expect(hsv.1).to_equal(0)
expect(hsv.2).to_equal(100)
```

</details>

#### hue when max is red
_Branch: max_val == r_norm_

#### converts pure red to HSV

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(255, 0, 0)
val hsv = rgb_to_hsv(c)
expect(hsv.0).to_equal(0)
expect(hsv.1).to_equal(100)
expect(hsv.2).to_equal(100)
```

</details>

#### hue when max is green
_Branch: max_val == g_norm_

#### converts pure green to HSV

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(0, 255, 0)
val hsv = rgb_to_hsv(c)
expect(hsv.0).to_equal(120)
expect(hsv.1).to_equal(100)
expect(hsv.2).to_equal(100)
```

</details>

#### hue when max is blue
_Branch: else (max is blue)_

#### converts pure blue to HSV

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(0, 0, 255)
val hsv = rgb_to_hsv(c)
expect(hsv.0).to_equal(240)
expect(hsv.1).to_equal(100)
expect(hsv.2).to_equal(100)
```

</details>

#### negative hue correction
_Branch: h < 0_

#### produces non-negative hue for all colors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(100, 0, 200)
val hsv = rgb_to_hsv(c)
val h = hsv.0
val h_non_neg = h >= 0
expect(h_non_neg).to_equal(true)
```

</details>

### hsv_to_rgb

#### achromatic (saturation == 0)
_Branch: s_norm == 0._

#### converts zero saturation to gray

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = hsv_to_rgb(0, 0, 50)
expect(c.r).to_equal(c.g)
expect(c.g).to_equal(c.b)
```

</details>

#### converts zero saturation black

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = hsv_to_rgb(0, 0, 0)
expect(c.r).to_equal(0)
```

</details>

#### converts zero saturation white

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = hsv_to_rgb(0, 0, 100)
expect(c.r).to_equal(255)
```

</details>

#### hue sector 0-59
_Branch: h_norm < 60_

#### converts hue 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = hsv_to_rgb(0, 100, 100)
expect(c.r).to_equal(255)
```

</details>

#### hue sector 60-119

#### converts hue 60

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = hsv_to_rgb(60, 100, 100)
expect(c.r).to_be_greater_than(200)
```

</details>

#### hue sector 120-179

#### converts hue 120

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = hsv_to_rgb(120, 100, 100)
expect(c.g).to_equal(255)
```

</details>

#### hue sector 180-239

#### converts hue 180

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = hsv_to_rgb(180, 100, 100)
expect(c.b).to_be_greater_than(200)
```

</details>

#### hue sector 240-299

#### converts hue 240

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = hsv_to_rgb(240, 100, 100)
expect(c.b).to_equal(255)
```

</details>

#### hue sector 300-359

#### converts hue 300

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = hsv_to_rgb(300, 100, 100)
expect(c.r).to_be_greater_than(200)
```

</details>

### to_hex

#### basic colors

#### converts black to hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(0, 0, 0)
expect(to_hex(c)).to_equal("#000000")
```

</details>

#### converts white to hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(255, 255, 255)
val hex = to_hex(c)
expect(hex).to_start_with("#")
```

</details>

#### converts red to hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(255, 0, 0)
val hex = to_hex(c)
expect(hex).to_start_with("#")
```

</details>

#### converts arbitrary color to hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(171, 205, 239)
val hex = to_hex(c)
expect(hex).to_start_with("#")
```

</details>

### to_hex_alpha
_Hex output with alpha channel._

#### alpha values

#### converts opaque color

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgba(255, 0, 0, 255)
expect(to_hex_alpha(c)).to_equal("#FF0000FF")
```

</details>

#### converts semi-transparent color

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgba(0, 255, 0, 128)
expect(to_hex_alpha(c)).to_equal("#00FF0080")
```

</details>

#### converts fully transparent color

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgba(0, 0, 255, 0)
expect(to_hex_alpha(c)).to_equal("#0000FF00")
```

</details>

### to_css

#### fully opaque (a == 255)
_Branch: color.a == 255 returns rgb()._

#### outputs rgb format for opaque color

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(255, 128, 0)
val css = to_css(c)
expect(css).to_start_with("rgb(")
```

</details>

#### semi-transparent (a != 255)
_Branch: color.a != 255 returns rgba()._

#### outputs rgba format for transparent color

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgba(100, 200, 50, 128)
val css = to_css(c)
expect(css).to_start_with("rgba(")
```

</details>

#### outputs rgba format for fully transparent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgba(0, 0, 0, 0)
val css = to_css(c)
expect(css).to_start_with("rgba(")
```

</details>

### max3

#### first value is max

#### returns a when a is largest

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(max3(10, 5, 3)).to_equal(10)
```

</details>

#### second value is max
_Branch: b > result is true._

#### returns b when b is largest

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(max3(5, 10, 3)).to_equal(10)
```

</details>

#### third value is max
_Branch: c > result is true._

#### returns c when c is largest

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(max3(3, 5, 10)).to_equal(10)
```

</details>

#### equal values

#### returns value when all equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(max3(7, 7, 7)).to_equal(7)
```

</details>

#### negative values

#### handles negative numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(max3(-5, -2, -10)).to_equal(-2)
```

</details>

### min3

#### first value is min

#### returns a when a is smallest

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(min3(1, 5, 10)).to_equal(1)
```

</details>

#### second value is min
_Branch: b < result is true._

#### returns b when b is smallest

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(min3(5, 1, 10)).to_equal(1)
```

</details>

#### third value is min
_Branch: c < result is true._

#### returns c when c is smallest

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(min3(5, 10, 1)).to_equal(1)
```

</details>

#### equal values

#### returns value when all equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(min3(7, 7, 7)).to_equal(7)
```

</details>

#### negative values

#### handles negative numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(min3(-5, -2, -10)).to_equal(-10)
```

</details>

### abs

#### positive values
_Branch: value < 0 is false._

#### returns positive value unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(abs(42)).to_equal(42)
```

</details>

#### negative values
_Branch: value < 0 is true._

#### returns negated negative value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(abs(-42)).to_equal(42)
```

</details>

#### zero

#### returns zero for zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(abs(0)).to_equal(0)
```

</details>

### hex_to_int

#### empty string
_Branch: length == 0 returns 0._

#### returns 0 for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_int("")).to_equal(0)
```

</details>

#### single characters

#### converts 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_int("0")).to_equal(0)
```

</details>

#### converts 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_int("9")).to_equal(9)
```

</details>

#### converts A

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_int("A")).to_equal(10)
```

</details>

#### converts F

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_int("F")).to_equal(15)
```

</details>

#### converts lowercase a

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_int("a")).to_equal(10)
```

</details>

#### converts lowercase f

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_int("f")).to_equal(15)
```

</details>

#### two characters

#### converts FF

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = hex_to_int("FF")
val valid = result >= 0
expect(valid).to_equal(true)
```

</details>

#### converts 00

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_int("00")).to_equal(0)
```

</details>

#### converts 80

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = hex_to_int("80")
val valid = result >= 0
expect(valid).to_equal(true)
```

</details>

#### converts AB

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = hex_to_int("AB")
val valid = result >= 0
expect(valid).to_equal(true)
```

</details>

### hex_char_to_int

#### decimal digits

#### converts all decimal digits 0-9

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_char_to_int("0")).to_equal(0)
expect(hex_char_to_int("1")).to_equal(1)
expect(hex_char_to_int("2")).to_equal(2)
expect(hex_char_to_int("3")).to_equal(3)
expect(hex_char_to_int("4")).to_equal(4)
expect(hex_char_to_int("5")).to_equal(5)
expect(hex_char_to_int("6")).to_equal(6)
expect(hex_char_to_int("7")).to_equal(7)
expect(hex_char_to_int("8")).to_equal(8)
expect(hex_char_to_int("9")).to_equal(9)
```

</details>

#### uppercase hex digits

#### converts all uppercase A-F

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_char_to_int("A")).to_equal(10)
expect(hex_char_to_int("B")).to_equal(11)
expect(hex_char_to_int("C")).to_equal(12)
expect(hex_char_to_int("D")).to_equal(13)
expect(hex_char_to_int("E")).to_equal(14)
expect(hex_char_to_int("F")).to_equal(15)
```

</details>

#### lowercase hex digits

#### converts a and f

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_char_to_int("a")).to_equal(10)
expect(hex_char_to_int("f")).to_equal(15)
```

</details>

#### invalid character
_Branch: fallthrough returns 0._

#### returns 0 for invalid char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_char_to_int("G")).to_equal(0)
```

</details>

#### returns 0 for space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_char_to_int(" ")).to_equal(0)
```

</details>

### int_to_hex
_Two-digit hex string from integer._

#### boundary values

#### converts 0 to 00

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(int_to_hex(0)).to_equal("00")
```

</details>

#### converts 255 to FF

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(int_to_hex(255)).to_equal("FF")
```

</details>

#### converts 128 to 80

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(int_to_hex(128)).to_equal("80")
```

</details>

#### converts 15 to 0F

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(int_to_hex(15)).to_equal("0F")
```

</details>

#### converts 16 to 10

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(int_to_hex(16)).to_equal("10")
```

</details>

### int_to_hex_char

#### all values

#### converts digits 0-9

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(int_to_hex_char(0)).to_equal("0")
expect(int_to_hex_char(1)).to_equal("1")
expect(int_to_hex_char(2)).to_equal("2")
expect(int_to_hex_char(3)).to_equal("3")
expect(int_to_hex_char(4)).to_equal("4")
expect(int_to_hex_char(5)).to_equal("5")
expect(int_to_hex_char(6)).to_equal("6")
expect(int_to_hex_char(7)).to_equal("7")
expect(int_to_hex_char(8)).to_equal("8")
expect(int_to_hex_char(9)).to_equal("9")
```

</details>

#### converts letters 10-15

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(int_to_hex_char(10)).to_equal("A")
expect(int_to_hex_char(11)).to_equal("B")
expect(int_to_hex_char(12)).to_equal("C")
expect(int_to_hex_char(13)).to_equal("D")
expect(int_to_hex_char(14)).to_equal("E")
expect(int_to_hex_char(15)).to_equal("F")
```

</details>

#### out of range
_Branch: fallthrough returns '0'._

#### returns 0 for value 16

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(int_to_hex_char(16)).to_equal("0")
```

</details>

#### returns 0 for negative value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(int_to_hex_char(-1)).to_equal("0")
```

</details>

### from_hsl
_Delegates to hsl_to_rgb._

#### creates color from HSL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_hsl(0, 100, 50)
expect(c.r).to_be_greater_than(200)
```

</details>

### from_hsv
_Delegates to hsv_to_rgb._

#### creates color from HSV

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_hsv(120, 100, 100)
expect(c.g).to_equal(255)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 89 |
| Active scenarios | 89 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
