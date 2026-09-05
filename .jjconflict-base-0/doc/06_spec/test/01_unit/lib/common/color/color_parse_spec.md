# Color Parse and Utilities Specification

> Tests for parse validation functions (is_valid_hex, is_valid_rgb, is_valid_hsl, is_valid_hsv, is_hex_char) and color utility functions (luminance, contrast_ratio, is_dark, is_light, is_accessible, color_distance, is_similar, web_safe, snap_to_web_safe).

<!-- sdn-diagram:id=color_parse_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=color_parse_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

color_parse_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=color_parse_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 62 | 62 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Color Parse and Utilities Specification

Tests for parse validation functions (is_valid_hex, is_valid_rgb, is_valid_hsl, is_valid_hsv, is_hex_char) and color utility functions (luminance, contrast_ratio, is_dark, is_light, is_accessible, color_distance, is_similar, web_safe, snap_to_web_safe).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COLOR-CVG |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/lib/common/color/color_parse_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for parse validation functions (is_valid_hex, is_valid_rgb, is_valid_hsl,
is_valid_hsv, is_hex_char) and color utility functions (luminance, contrast_ratio,
is_dark, is_light, is_accessible, color_distance, is_similar, web_safe,
snap_to_web_safe).

## Scenarios

### is_valid_hex

#### valid hex strings

#### validates 3-char hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = is_hex_char("A") and is_hex_char("B") and is_hex_char("C")
expect(valid).to_equal(true)
```

</details>

#### validates 4-char hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = is_hex_char("A") and is_hex_char("D")
expect(valid).to_equal(true)
```

</details>

#### validates 6-char hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = is_hex_char("A") and is_hex_char("B") and is_hex_char("C")
expect(valid).to_equal(true)
```

</details>

#### validates 8-char hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = is_hex_char("A") and is_hex_char("D")
expect(valid).to_equal(true)
```

</details>

#### validates without hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = is_hex_char("A")
expect(valid).to_equal(true)
```

</details>

#### validates lowercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = is_hex_char("a") and is_hex_char("f")
expect(valid).to_equal(true)
```

</details>

#### invalid lengths
_Branch: len != 3, 4, 6, 8 returns false._

#### rejects 1-char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_hex("#A")).to_equal(false)
```

</details>

#### rejects 2-char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_hex("#AB")).to_equal(false)
```

</details>

#### rejects 5-char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_hex("#ABCDE")).to_equal(false)
```

</details>

#### rejects 7-char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_hex("#ABCDEFF")).to_equal(false)
```

</details>

#### invalid characters
_Branch: is_hex_char returns false during loop._

#### rejects G character

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_hex("#GGG")).to_equal(false)
```

</details>

#### rejects Z character

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_hex("#ZZZ")).to_equal(false)
```

</details>

#### hash prefix handling
_Branch: starts_with '#' true and false._

#### strips hash prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = is_hex_char("F")
expect(valid).to_equal(true)
```

</details>

#### works without hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = is_hex_char("F")
expect(valid).to_equal(true)
```

</details>

### is_valid_rgb

#### validates in-range values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_rgb(0, 128, 255)).to_equal(true)
```

</details>

#### rejects negative r

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_rgb(-1, 0, 0)).to_equal(false)
```

</details>

#### rejects r above 255

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_rgb(256, 0, 0)).to_equal(false)
```

</details>

#### validates boundary 0 0 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_rgb(0, 0, 0)).to_equal(true)
```

</details>

### is_valid_hsl
_HSL Range Validation._

#### validates in-range values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_hsl(180, 50, 50)).to_equal(true)
```

</details>

#### rejects out-of-range h

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_hsl(360, 50, 50)).to_equal(false)
```

</details>

#### rejects out-of-range s

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_hsl(0, 101, 50)).to_equal(false)
```

</details>

### is_valid_hsv
_HSV Range Validation._

#### validates in-range values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_hsv(180, 50, 50)).to_equal(true)
```

</details>

#### rejects out-of-range h

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_hsv(360, 50, 50)).to_equal(false)
```

</details>

#### rejects out-of-range v

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_hsv(0, 50, 101)).to_equal(false)
```

</details>

### is_hex_char

#### valid digits

#### validates all decimal digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char("0")).to_equal(true)
expect(is_hex_char("1")).to_equal(true)
expect(is_hex_char("2")).to_equal(true)
expect(is_hex_char("3")).to_equal(true)
expect(is_hex_char("4")).to_equal(true)
expect(is_hex_char("5")).to_equal(true)
expect(is_hex_char("6")).to_equal(true)
expect(is_hex_char("7")).to_equal(true)
expect(is_hex_char("8")).to_equal(true)
expect(is_hex_char("9")).to_equal(true)
```

</details>

#### validates all uppercase hex letters

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char("A")).to_equal(true)
expect(is_hex_char("B")).to_equal(true)
expect(is_hex_char("C")).to_equal(true)
expect(is_hex_char("D")).to_equal(true)
expect(is_hex_char("E")).to_equal(true)
expect(is_hex_char("F")).to_equal(true)
```

</details>

#### validates lowercase a and f

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char("a")).to_equal(true)
expect(is_hex_char("f")).to_equal(true)
```

</details>

#### invalid characters
_Branch: all checks fail, returns false._

#### rejects G

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char("G")).to_equal(false)
```

</details>

#### rejects Z

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char("Z")).to_equal(false)
```

</details>

#### rejects space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char(" ")).to_equal(false)
```

</details>

### luminance

#### black has zero luminance

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(0, 0, 0)
expect(luminance(c)).to_equal(0)
```

</details>

#### white has luminance near 100

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(255, 255, 255)
val lum = luminance(c)
val near_100 = lum >= 95
expect(near_100).to_equal(true)
```

</details>

#### red has lower luminance than white

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val red_lum = luminance(from_rgb(255, 0, 0))
val white_lum = luminance(from_rgb(255, 255, 255))
val less = red_lum < white_lum
expect(less).to_equal(true)
```

</details>

### contrast_ratio

#### high contrast

#### black vs white has maximum contrast

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ratio = contrast_ratio(from_rgb(0, 0, 0), from_rgb(255, 255, 255))
val high = ratio > 1000
expect(high).to_equal(true)
```

</details>

#### l2 > l1 branch
_Branch: l2 > l1 swaps lighter/darker._

#### is symmetric

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Use pure black and white for reliable luminance values
val c1 = from_rgb(0, 0, 0)
val c2 = from_rgb(255, 255, 255)
val r1 = contrast_ratio(c1, c2)
val r2 = contrast_ratio(c2, c1)
expect(r1).to_equal(r2)
```

</details>

#### darker == 0 branch
_Branch: darker == 0 returns 2100._

#### returns 2100 when darker luminance is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ratio = contrast_ratio(from_rgb(255, 255, 255), from_rgb(0, 0, 0))
expect(ratio).to_equal(2100)
```

</details>

### is_dark

#### black is dark

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_dark(from_rgb(0, 0, 0))).to_equal(true)
```

</details>

#### white is not dark

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_dark(from_rgb(255, 255, 255))).to_equal(false)
```

</details>

#### dark gray is dark

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_dark(from_rgb(50, 50, 50))).to_equal(true)
```

</details>

### is_light

#### white is light

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_light(from_rgb(255, 255, 255))).to_equal(true)
```

</details>

#### black is not light

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_light(from_rgb(0, 0, 0))).to_equal(false)
```

</details>

#### light gray is light

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_light(from_rgb(200, 200, 200))).to_equal(true)
```

</details>

### is_accessible

#### AA level (default)

#### black on white passes AA

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_accessible(from_rgb(0, 0, 0), from_rgb(255, 255, 255), "AA")
expect(result).to_equal(true)
```

</details>

#### similar colors fail AA

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_accessible(from_rgb(200, 200, 200), from_rgb(210, 210, 210), "AA")
expect(result).to_equal(false)
```

</details>

#### AAA level
_Branch: level == 'AAA' uses ratio >= 700._

#### black on white passes AAA

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_accessible(from_rgb(0, 0, 0), from_rgb(255, 255, 255), "AAA")
expect(result).to_equal(true)
```

</details>

#### similar colors fail AAA

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_accessible(from_rgb(200, 200, 200), from_rgb(220, 220, 220), "AAA")
expect(result).to_equal(false)
```

</details>

### color_distance
_Euclidean distance in RGB space (squared)._

#### same color has zero distance

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(100, 100, 100)
expect(color_distance(c, c)).to_equal(0)
```

</details>

#### black to white has large distance

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dist = color_distance(from_rgb(0, 0, 0), from_rgb(255, 255, 255))
val large = dist > 100000
expect(large).to_equal(true)
```

</details>

### is_similar

#### identical colors are similar

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = from_rgb(100, 100, 100)
expect(is_similar(c, c, 0)).to_equal(true)
```

</details>

#### very different colors are not similar with low threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = from_rgb(0, 0, 0)
val c2 = from_rgb(255, 255, 255)
expect(is_similar(c1, c2, 100)).to_equal(false)
```

</details>

#### slightly different colors are similar with high threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = from_rgb(100, 100, 100)
val c2 = from_rgb(105, 105, 105)
expect(is_similar(c1, c2, 1000)).to_equal(true)
```

</details>

### web_safe
_Snap color to web-safe palette._

#### snaps black to black

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = web_safe(from_rgb(0, 0, 0))
expect(c.r).to_equal(0)
expect(c.g).to_equal(0)
expect(c.b).to_equal(0)
```

</details>

#### snaps white to white

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = web_safe(from_rgb(255, 255, 255))
expect(c.r).to_equal(255)
expect(c.g).to_equal(255)
```

</details>

#### snaps intermediate value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = web_safe(from_rgb(100, 100, 100))
expect(c.r).to_equal(102)
```

</details>

### snap_to_web_safe

#### snaps 0 to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(snap_to_web_safe(0)).to_equal(0)
```

</details>

#### snaps 25 to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(snap_to_web_safe(25)).to_equal(0)
```

</details>

#### snaps 26 to 51

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(snap_to_web_safe(26)).to_equal(51)
```

</details>

#### snaps 51 to 51

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(snap_to_web_safe(51)).to_equal(51)
```

</details>

#### snaps 76 to 51

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(snap_to_web_safe(76)).to_equal(51)
```

</details>

#### snaps 77 to 102

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(snap_to_web_safe(77)).to_equal(102)
```

</details>

#### snaps 255 to 255

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(snap_to_web_safe(255)).to_equal(255)
```

</details>

#### snaps 230 to 255

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(snap_to_web_safe(230)).to_equal(255)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 62 |
| Active scenarios | 62 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
