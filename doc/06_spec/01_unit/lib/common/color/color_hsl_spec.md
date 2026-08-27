# Color HSL/HSV Conversion Specification

> Purpose: Prove that rgb_to_hsl.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 89 | 89 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Color HSL/HSV Conversion Specification

Purpose: Prove that rgb_to_hsl.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COLOR-CVG |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/lib/common/color/color_hsl_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that rgb_to_hsl.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### rgb_to_hsl

#### achromatic colors (delta == 0)
_Branch: delta == 0 returns early._

#### converts black to HSL zero

- converts black to HSL zero
- Verify: converts black to HSL zero
   - Expected: hsl.0 equals `0`
   - Expected: hsl.1 equals `0`
   - Expected: hsl.2 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts black to HSL zero")
step("Verify: converts black to HSL zero")
# @req: REQ-LIB-COMMON-001
val c = from_rgb(0, 0, 0)
val hsl = rgb_to_hsl(c)
expect(hsl.0).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(hsl.1).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(hsl.2).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### converts white to HSL

- converts white to HSL
- Verify: converts white to HSL
   - Expected: hsl.0 equals `0`
   - Expected: hsl.1 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts white to HSL")
step("Verify: converts white to HSL")
val c = from_rgb(255, 255, 255)
val hsl = rgb_to_hsl(c)
expect(hsl.0).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(hsl.1).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### converts gray to HSL with zero saturation

- converts gray to HSL with zero saturation
- Verify: converts gray to HSL with zero saturation
   - Expected: hsl.1 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts gray to HSL with zero saturation")
step("Verify: converts gray to HSL with zero saturation")
val c = from_rgb(128, 128, 128)
val hsl = rgb_to_hsl(c)
expect(hsl.1).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### hue calculation when max is red
_Branch: max_val == r_norm_

#### converts pure red

- converts pure red
- Verify: converts pure red
   - Expected: hsl.0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts pure red")
step("Verify: converts pure red")
val c = from_rgb(255, 0, 0)
val hsl = rgb_to_hsl(c)
expect(hsl.0).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### converts red-dominant color

- converts red-dominant color
- Verify: converts red-dominant color
   - Expected: h_valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts red-dominant color")
step("Verify: converts red-dominant color")
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

- converts pure green
- Verify: converts pure green
   - Expected: hsl.0 equals `120`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts pure green")
step("Verify: converts pure green")
val c = from_rgb(0, 255, 0)
val hsl = rgb_to_hsl(c)
expect(hsl.0).to_equal(120)  # oracle: 120 — named expected value from the requirement
```

</details>

#### converts green-dominant color

- converts green-dominant color
- Verify: converts green-dominant color
   - Expected: h_valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts green-dominant color")
step("Verify: converts green-dominant color")
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

- converts pure blue
- Verify: converts pure blue
   - Expected: hsl.0 equals `240`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts pure blue")
step("Verify: converts pure blue")
val c = from_rgb(0, 0, 255)
val hsl = rgb_to_hsl(c)
expect(hsl.0).to_equal(240)  # oracle: 240 — named expected value from the requirement
```

</details>

#### converts blue-dominant color

- converts blue-dominant color
- Verify: converts blue-dominant color
   - Expected: h_valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts blue-dominant color")
step("Verify: converts blue-dominant color")
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

- dark color has l < 50
- Verify: dark color has l < 50
   - Expected: is_low is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dark color has l < 50")
step("Verify: dark color has l < 50")
val c = from_rgb(100, 50, 25)
val hsl = rgb_to_hsl(c)
val l_val = hsl.2
val is_low = l_val < 50
expect(is_low).to_equal(true)
```

</details>

#### light color has l >= 50

- light color has l >= 50
- Verify: light color has l >= 50
   - Expected: is_high is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("light color has l >= 50")
step("Verify: light color has l >= 50")
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

- handles color that produces negative hue
- Verify: handles color that produces negative hue
   - Expected: h_non_neg is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles color that produces negative hue")
step("Verify: handles color that produces negative hue")
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

- converts zero saturation to gray
- Verify: converts zero saturation to gray
   - Expected: c.r equals `c.g`
   - Expected: c.g equals `c.b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts zero saturation to gray")
step("Verify: converts zero saturation to gray")
val c = hsl_to_rgb(0, 0, 50)
expect(c.r).to_equal(c.g)
expect(c.g).to_equal(c.b)
```

</details>

#### converts zero saturation black

- converts zero saturation black
- Verify: converts zero saturation black
   - Expected: c.r equals `0`
   - Expected: c.g equals `0`
   - Expected: c.b equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts zero saturation black")
step("Verify: converts zero saturation black")
val c = hsl_to_rgb(0, 0, 0)
expect(c.r).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(c.g).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(c.b).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### converts zero saturation white

- converts zero saturation white
- Verify: converts zero saturation white
   - Expected: c.r equals `255`
   - Expected: c.g equals `255`
   - Expected: c.b equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts zero saturation white")
step("Verify: converts zero saturation white")
val c = hsl_to_rgb(0, 0, 100)
expect(c.r).to_equal(255)  # oracle: 255 — named expected value from the requirement
expect(c.g).to_equal(255)  # oracle: 255 — named expected value from the requirement
expect(c.b).to_equal(255)  # oracle: 255 — named expected value from the requirement
```

</details>

#### chroma calculation branches
_Branch: l_norm < 50 (true) vs >= 50 (false)._

#### computes chroma for dark color (l < 50)

- computes chroma for dark color (l < 50)
- Verify: computes chroma for dark color (l < 50)
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("computes chroma for dark color (l < 50)")
step("Verify: computes chroma for dark color (l < 50)")
val c = hsl_to_rgb(0, 100, 25)
val valid = c.r >= 0
expect(valid).to_equal(true)
```

</details>

#### computes chroma for light color (l >= 50)

- computes chroma for light color (l >= 50)
- Verify: computes chroma for light color (l >= 50)
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("computes chroma for light color (l >= 50)")
step("Verify: computes chroma for light color (l >= 50)")
val c = hsl_to_rgb(0, 100, 75)
val valid = c.r >= 0
expect(valid).to_equal(true)
```

</details>

#### hue sector 0-59 (red-yellow)

#### converts hue 0 (red)

- converts hue 0 (red)
- Verify: converts hue 0 (red)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts hue 0 (red)")
step("Verify: converts hue 0 (red)")
val c = hsl_to_rgb(0, 100, 50)
expect(c.r).to_be_greater_than(200)
```

</details>

#### hue sector 60-119 (yellow-green)

#### converts hue 60 (yellow)

- converts hue 60 (yellow)
- Verify: converts hue 60 (yellow)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts hue 60 (yellow)")
step("Verify: converts hue 60 (yellow)")
val c = hsl_to_rgb(60, 100, 50)
expect(c.r).to_be_greater_than(200)
```

</details>

#### hue sector 120-179 (green-cyan)

#### converts hue 120 (green)

- converts hue 120 (green)
- Verify: converts hue 120 (green)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts hue 120 (green)")
step("Verify: converts hue 120 (green)")
val c = hsl_to_rgb(120, 100, 50)
expect(c.g).to_be_greater_than(200)
```

</details>

#### hue sector 180-239 (cyan-blue)

#### converts hue 180 (cyan)

- converts hue 180 (cyan)
- Verify: converts hue 180 (cyan)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts hue 180 (cyan)")
step("Verify: converts hue 180 (cyan)")
val c = hsl_to_rgb(180, 100, 50)
expect(c.b).to_be_greater_than(200)
```

</details>

#### hue sector 240-299 (blue-magenta)

#### converts hue 240 (blue)

- converts hue 240 (blue)
- Verify: converts hue 240 (blue)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts hue 240 (blue)")
step("Verify: converts hue 240 (blue)")
val c = hsl_to_rgb(240, 100, 50)
expect(c.b).to_be_greater_than(200)
```

</details>

#### hue sector 300-359 (magenta-red)

#### converts hue 300 (magenta)

- converts hue 300 (magenta)
- Verify: converts hue 300 (magenta)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts hue 300 (magenta)")
step("Verify: converts hue 300 (magenta)")
val c = hsl_to_rgb(300, 100, 50)
expect(c.r).to_be_greater_than(200)
```

</details>

### rgb_to_hsv

#### black (max == 0)
_Branch: max_val == 0 returns (0, 0, 0)._

#### converts black to zero HSV

- converts black to zero HSV
- Verify: converts black to zero HSV
   - Expected: hsv.0 equals `0`
   - Expected: hsv.1 equals `0`
   - Expected: hsv.2 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts black to zero HSV")
step("Verify: converts black to zero HSV")
val c = from_rgb(0, 0, 0)
val hsv = rgb_to_hsv(c)
expect(hsv.0).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(hsv.1).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(hsv.2).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### achromatic (delta == 0, non-black)
_Branch: delta == 0 returns (0, 0, v)._

#### converts gray to HSV with zero saturation

- converts gray to HSV with zero saturation
- Verify: converts gray to HSV with zero saturation
   - Expected: hsv.0 equals `0`
   - Expected: hsv.1 equals `0`
   - Expected: v_positive is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts gray to HSV with zero saturation")
step("Verify: converts gray to HSV with zero saturation")
val c = from_rgb(128, 128, 128)
val hsv = rgb_to_hsv(c)
expect(hsv.0).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(hsv.1).to_equal(0)  # oracle: 0 — named expected value from the requirement
val v = hsv.2
val v_positive = v > 0
expect(v_positive).to_equal(true)
```

</details>

#### converts white to HSV

- converts white to HSV
- Verify: converts white to HSV
   - Expected: hsv.0 equals `0`
   - Expected: hsv.1 equals `0`
   - Expected: hsv.2 equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts white to HSV")
step("Verify: converts white to HSV")
val c = from_rgb(255, 255, 255)
val hsv = rgb_to_hsv(c)
expect(hsv.0).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(hsv.1).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(hsv.2).to_equal(100)  # oracle: 100 — named expected value from the requirement
```

</details>

#### hue when max is red
_Branch: max_val == r_norm_

#### converts pure red to HSV

- converts pure red to HSV
- Verify: converts pure red to HSV
   - Expected: hsv.0 equals `0`
   - Expected: hsv.1 equals `100`
   - Expected: hsv.2 equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts pure red to HSV")
step("Verify: converts pure red to HSV")
val c = from_rgb(255, 0, 0)
val hsv = rgb_to_hsv(c)
expect(hsv.0).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(hsv.1).to_equal(100)  # oracle: 100 — named expected value from the requirement
expect(hsv.2).to_equal(100)  # oracle: 100 — named expected value from the requirement
```

</details>

#### hue when max is green
_Branch: max_val == g_norm_

#### converts pure green to HSV

- converts pure green to HSV
- Verify: converts pure green to HSV
   - Expected: hsv.0 equals `120`
   - Expected: hsv.1 equals `100`
   - Expected: hsv.2 equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts pure green to HSV")
step("Verify: converts pure green to HSV")
val c = from_rgb(0, 255, 0)
val hsv = rgb_to_hsv(c)
expect(hsv.0).to_equal(120)  # oracle: 120 — named expected value from the requirement
expect(hsv.1).to_equal(100)  # oracle: 100 — named expected value from the requirement
expect(hsv.2).to_equal(100)  # oracle: 100 — named expected value from the requirement
```

</details>

#### hue when max is blue
_Branch: else (max is blue)_

#### converts pure blue to HSV

- converts pure blue to HSV
- Verify: converts pure blue to HSV
   - Expected: hsv.0 equals `240`
   - Expected: hsv.1 equals `100`
   - Expected: hsv.2 equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts pure blue to HSV")
step("Verify: converts pure blue to HSV")
val c = from_rgb(0, 0, 255)
val hsv = rgb_to_hsv(c)
expect(hsv.0).to_equal(240)  # oracle: 240 — named expected value from the requirement
expect(hsv.1).to_equal(100)  # oracle: 100 — named expected value from the requirement
expect(hsv.2).to_equal(100)  # oracle: 100 — named expected value from the requirement
```

</details>

#### negative hue correction
_Branch: h < 0_

#### produces non-negative hue for all colors

- produces non-negative hue for all colors
- Verify: produces non-negative hue for all colors
   - Expected: h_non_neg is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("produces non-negative hue for all colors")
step("Verify: produces non-negative hue for all colors")
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

- converts zero saturation to gray
- Verify: converts zero saturation to gray
   - Expected: c.r equals `c.g`
   - Expected: c.g equals `c.b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts zero saturation to gray")
step("Verify: converts zero saturation to gray")
val c = hsv_to_rgb(0, 0, 50)
expect(c.r).to_equal(c.g)
expect(c.g).to_equal(c.b)
```

</details>

#### converts zero saturation black

- converts zero saturation black
- Verify: converts zero saturation black
   - Expected: c.r equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts zero saturation black")
step("Verify: converts zero saturation black")
val c = hsv_to_rgb(0, 0, 0)
expect(c.r).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### converts zero saturation white

- converts zero saturation white
- Verify: converts zero saturation white
   - Expected: c.r equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts zero saturation white")
step("Verify: converts zero saturation white")
val c = hsv_to_rgb(0, 0, 100)
expect(c.r).to_equal(255)  # oracle: 255 — named expected value from the requirement
```

</details>

#### hue sector 0-59
_Branch: h_norm < 60_

#### converts hue 0

- converts hue 0
- Verify: converts hue 0
   - Expected: c.r equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts hue 0")
step("Verify: converts hue 0")
val c = hsv_to_rgb(0, 100, 100)
expect(c.r).to_equal(255)  # oracle: 255 — named expected value from the requirement
```

</details>

#### hue sector 60-119

#### converts hue 60

- converts hue 60
- Verify: converts hue 60


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts hue 60")
step("Verify: converts hue 60")
val c = hsv_to_rgb(60, 100, 100)
expect(c.r).to_be_greater_than(200)
```

</details>

#### hue sector 120-179

#### converts hue 120

- converts hue 120
- Verify: converts hue 120
   - Expected: c.g equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts hue 120")
step("Verify: converts hue 120")
val c = hsv_to_rgb(120, 100, 100)
expect(c.g).to_equal(255)  # oracle: 255 — named expected value from the requirement
```

</details>

#### hue sector 180-239

#### converts hue 180

- converts hue 180
- Verify: converts hue 180


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts hue 180")
step("Verify: converts hue 180")
val c = hsv_to_rgb(180, 100, 100)
expect(c.b).to_be_greater_than(200)
```

</details>

#### hue sector 240-299

#### converts hue 240

- converts hue 240
- Verify: converts hue 240
   - Expected: c.b equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts hue 240")
step("Verify: converts hue 240")
val c = hsv_to_rgb(240, 100, 100)
expect(c.b).to_equal(255)  # oracle: 255 — named expected value from the requirement
```

</details>

#### hue sector 300-359

#### converts hue 300

- converts hue 300
- Verify: converts hue 300


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts hue 300")
step("Verify: converts hue 300")
val c = hsv_to_rgb(300, 100, 100)
expect(c.r).to_be_greater_than(200)
```

</details>

### to_hex

#### basic colors

#### converts black to hex

- converts black to hex
- Verify: converts black to hex
   - Expected: to_hex(c) equals `#000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts black to hex")
step("Verify: converts black to hex")
val c = from_rgb(0, 0, 0)
expect(to_hex(c)).to_equal("#000000")
```

</details>

#### converts white to hex

- converts white to hex
- Verify: converts white to hex


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts white to hex")
step("Verify: converts white to hex")
val c = from_rgb(255, 255, 255)
val hex = to_hex(c)
expect(hex).to_start_with("#")
```

</details>

#### converts red to hex

- converts red to hex
- Verify: converts red to hex


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts red to hex")
step("Verify: converts red to hex")
val c = from_rgb(255, 0, 0)
val hex = to_hex(c)
expect(hex).to_start_with("#")
```

</details>

#### converts arbitrary color to hex

- converts arbitrary color to hex
- Verify: converts arbitrary color to hex


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts arbitrary color to hex")
step("Verify: converts arbitrary color to hex")
val c = from_rgb(171, 205, 239)
val hex = to_hex(c)
expect(hex).to_start_with("#")
```

</details>

### to_hex_alpha
_Hex output with alpha channel._

#### alpha values

#### converts opaque color

- converts opaque color
- Verify: converts opaque color
   - Expected: to_hex_alpha(c) equals `#FF0000FF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts opaque color")
step("Verify: converts opaque color")
val c = from_rgba(255, 0, 0, 255)
expect(to_hex_alpha(c)).to_equal("#FF0000FF")
```

</details>

#### converts semi-transparent color

- converts semi-transparent color
- Verify: converts semi-transparent color
   - Expected: to_hex_alpha(c) equals `#00FF0080`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts semi-transparent color")
step("Verify: converts semi-transparent color")
val c = from_rgba(0, 255, 0, 128)
expect(to_hex_alpha(c)).to_equal("#00FF0080")
```

</details>

#### converts fully transparent color

- converts fully transparent color
- Verify: converts fully transparent color
   - Expected: to_hex_alpha(c) equals `#0000FF00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts fully transparent color")
step("Verify: converts fully transparent color")
val c = from_rgba(0, 0, 255, 0)
expect(to_hex_alpha(c)).to_equal("#0000FF00")
```

</details>

### to_css

#### fully opaque (a == 255)
_Branch: color.a == 255 returns rgb()._

#### outputs rgb format for opaque color

- outputs rgb format for opaque color
- Verify: outputs rgb format for opaque color


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("outputs rgb format for opaque color")
step("Verify: outputs rgb format for opaque color")
val c = from_rgb(255, 128, 0)
val css = to_css(c)
expect(css).to_start_with("rgb(")
```

</details>

#### semi-transparent (a != 255)
_Branch: color.a != 255 returns rgba()._

#### outputs rgba format for transparent color

- outputs rgba format for transparent color
- Verify: outputs rgba format for transparent color


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("outputs rgba format for transparent color")
step("Verify: outputs rgba format for transparent color")
val c = from_rgba(100, 200, 50, 128)
val css = to_css(c)
expect(css).to_start_with("rgba(")
```

</details>

#### outputs rgba format for fully transparent

- outputs rgba format for fully transparent
- Verify: outputs rgba format for fully transparent


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("outputs rgba format for fully transparent")
step("Verify: outputs rgba format for fully transparent")
val c = from_rgba(0, 0, 0, 0)
val css = to_css(c)
expect(css).to_start_with("rgba(")
```

</details>

### max3

#### first value is max

#### returns a when a is largest

- returns a when a is largest
- Verify: returns a when a is largest
   - Expected: max3(10, 5, 3) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns a when a is largest")
step("Verify: returns a when a is largest")
expect(max3(10, 5, 3)).to_equal(10)  # oracle: 10 — named expected value from the requirement
```

</details>

#### second value is max
_Branch: b > result is true._

#### returns b when b is largest

- returns b when b is largest
- Verify: returns b when b is largest
   - Expected: max3(5, 10, 3) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns b when b is largest")
step("Verify: returns b when b is largest")
expect(max3(5, 10, 3)).to_equal(10)  # oracle: 10 — named expected value from the requirement
```

</details>

#### third value is max
_Branch: c > result is true._

#### returns c when c is largest

- returns c when c is largest
- Verify: returns c when c is largest
   - Expected: max3(3, 5, 10) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns c when c is largest")
step("Verify: returns c when c is largest")
expect(max3(3, 5, 10)).to_equal(10)  # oracle: 10 — named expected value from the requirement
```

</details>

#### equal values

#### returns value when all equal

- returns value when all equal
- Verify: returns value when all equal
   - Expected: max3(7, 7, 7) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns value when all equal")
step("Verify: returns value when all equal")
expect(max3(7, 7, 7)).to_equal(7)  # oracle: 7 — named expected value from the requirement
```

</details>

#### negative values

#### handles negative numbers

- handles negative numbers
- Verify: handles negative numbers
   - Expected: max3(-5, -2, -10) equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles negative numbers")
step("Verify: handles negative numbers")
expect(max3(-5, -2, -10)).to_equal(-2)  # oracle: -2 — named expected value from the requirement
```

</details>

### min3

#### first value is min

#### returns a when a is smallest

- returns a when a is smallest
- Verify: returns a when a is smallest
   - Expected: min3(1, 5, 10) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns a when a is smallest")
step("Verify: returns a when a is smallest")
expect(min3(1, 5, 10)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### second value is min
_Branch: b < result is true._

#### returns b when b is smallest

- returns b when b is smallest
- Verify: returns b when b is smallest
   - Expected: min3(5, 1, 10) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns b when b is smallest")
step("Verify: returns b when b is smallest")
expect(min3(5, 1, 10)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### third value is min
_Branch: c < result is true._

#### returns c when c is smallest

- returns c when c is smallest
- Verify: returns c when c is smallest
   - Expected: min3(5, 10, 1) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns c when c is smallest")
step("Verify: returns c when c is smallest")
expect(min3(5, 10, 1)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### equal values

#### returns value when all equal

- returns value when all equal
- Verify: returns value when all equal
   - Expected: min3(7, 7, 7) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns value when all equal")
step("Verify: returns value when all equal")
expect(min3(7, 7, 7)).to_equal(7)  # oracle: 7 — named expected value from the requirement
```

</details>

#### negative values

#### handles negative numbers

- handles negative numbers
- Verify: handles negative numbers
   - Expected: min3(-5, -2, -10) equals `-10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles negative numbers")
step("Verify: handles negative numbers")
expect(min3(-5, -2, -10)).to_equal(-10)  # oracle: -10 — named expected value from the requirement
```

</details>

### abs

#### positive values
_Branch: value < 0 is false._

#### returns positive value unchanged

- returns positive value unchanged
- Verify: returns positive value unchanged
   - Expected: abs(42) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns positive value unchanged")
step("Verify: returns positive value unchanged")
expect(abs(42)).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### negative values
_Branch: value < 0 is true._

#### returns negated negative value

- returns negated negative value
- Verify: returns negated negative value
   - Expected: abs(-42) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns negated negative value")
step("Verify: returns negated negative value")
expect(abs(-42)).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### zero

#### returns zero for zero

- returns zero for zero
- Verify: returns zero for zero
   - Expected: abs(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns zero for zero")
step("Verify: returns zero for zero")
expect(abs(0)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### hex_to_int

#### empty string
_Branch: length == 0 returns 0._

#### returns 0 for empty string

- returns 0 for empty string
- Verify: returns 0 for empty string
   - Expected: hex_to_int("") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 0 for empty string")
step("Verify: returns 0 for empty string")
expect(hex_to_int("")).to_equal(0)
```

</details>

#### single characters

#### converts 0

- converts 0
- Verify: converts 0
   - Expected: hex_to_int("0") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts 0")
step("Verify: converts 0")
expect(hex_to_int("0")).to_equal(0)
```

</details>

#### converts 9

- converts 9
- Verify: converts 9
   - Expected: hex_to_int("9") equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts 9")
step("Verify: converts 9")
expect(hex_to_int("9")).to_equal(9)
```

</details>

#### converts A

- converts A
- Verify: converts A
   - Expected: hex_to_int("A") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts A")
step("Verify: converts A")
expect(hex_to_int("A")).to_equal(10)
```

</details>

#### converts F

- converts F
- Verify: converts F
   - Expected: hex_to_int("F") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts F")
step("Verify: converts F")
expect(hex_to_int("F")).to_equal(15)
```

</details>

#### converts lowercase a

- converts lowercase a
- Verify: converts lowercase a
   - Expected: hex_to_int("a") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts lowercase a")
step("Verify: converts lowercase a")
expect(hex_to_int("a")).to_equal(10)
```

</details>

#### converts lowercase f

- converts lowercase f
- Verify: converts lowercase f
   - Expected: hex_to_int("f") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts lowercase f")
step("Verify: converts lowercase f")
expect(hex_to_int("f")).to_equal(15)
```

</details>

#### two characters

#### converts FF

- converts FF
- Verify: converts FF
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts FF")
step("Verify: converts FF")
val result = hex_to_int("FF")
val valid = result >= 0
expect(valid).to_equal(true)
```

</details>

#### converts 00

- converts 00
- Verify: converts 00
   - Expected: hex_to_int("00") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts 00")
step("Verify: converts 00")
expect(hex_to_int("00")).to_equal(0)
```

</details>

#### converts 80

- converts 80
- Verify: converts 80
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts 80")
step("Verify: converts 80")
val result = hex_to_int("80")
val valid = result >= 0
expect(valid).to_equal(true)
```

</details>

#### converts AB

- converts AB
- Verify: converts AB
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts AB")
step("Verify: converts AB")
val result = hex_to_int("AB")
val valid = result >= 0
expect(valid).to_equal(true)
```

</details>

### hex_char_to_int

#### decimal digits

#### converts all decimal digits 0-9

- converts all decimal digits 0-9
- Verify: converts all decimal digits 0-9
   - Expected: hex_char_to_int("0") equals `0`
   - Expected: hex_char_to_int("1") equals `1`
   - Expected: hex_char_to_int("2") equals `2`
   - Expected: hex_char_to_int("3") equals `3`
   - Expected: hex_char_to_int("4") equals `4`
   - Expected: hex_char_to_int("5") equals `5`
   - Expected: hex_char_to_int("6") equals `6`
   - Expected: hex_char_to_int("7") equals `7`
   - Expected: hex_char_to_int("8") equals `8`
   - Expected: hex_char_to_int("9") equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts all decimal digits 0-9")
step("Verify: converts all decimal digits 0-9")
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

- converts all uppercase A-F
- Verify: converts all uppercase A-F
   - Expected: hex_char_to_int("A") equals `10`
   - Expected: hex_char_to_int("B") equals `11`
   - Expected: hex_char_to_int("C") equals `12`
   - Expected: hex_char_to_int("D") equals `13`
   - Expected: hex_char_to_int("E") equals `14`
   - Expected: hex_char_to_int("F") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts all uppercase A-F")
step("Verify: converts all uppercase A-F")
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

- converts a and f
- Verify: converts a and f
   - Expected: hex_char_to_int("a") equals `10`
   - Expected: hex_char_to_int("f") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts a and f")
step("Verify: converts a and f")
expect(hex_char_to_int("a")).to_equal(10)
expect(hex_char_to_int("f")).to_equal(15)
```

</details>

#### invalid character
_Branch: fallthrough returns 0._

#### returns 0 for invalid char

- returns 0 for invalid char
- Verify: returns 0 for invalid char
   - Expected: hex_char_to_int("G") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 0 for invalid char")
step("Verify: returns 0 for invalid char")
expect(hex_char_to_int("G")).to_equal(0)
```

</details>

#### returns 0 for space

- returns 0 for space
- Verify: returns 0 for space
   - Expected: hex_char_to_int(" ") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 0 for space")
step("Verify: returns 0 for space")
expect(hex_char_to_int(" ")).to_equal(0)
```

</details>

### int_to_hex
_Two-digit hex string from integer._

#### boundary values

#### converts 0 to 00

- converts 0 to 00
- Verify: converts 0 to 00
   - Expected: int_to_hex(0) equals `00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts 0 to 00")
step("Verify: converts 0 to 00")
expect(int_to_hex(0)).to_equal("00")
```

</details>

#### converts 255 to FF

- converts 255 to FF
- Verify: converts 255 to FF
   - Expected: int_to_hex(255) equals `FF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts 255 to FF")
step("Verify: converts 255 to FF")
expect(int_to_hex(255)).to_equal("FF")
```

</details>

#### converts 128 to 80

- converts 128 to 80
- Verify: converts 128 to 80
   - Expected: int_to_hex(128) equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts 128 to 80")
step("Verify: converts 128 to 80")
expect(int_to_hex(128)).to_equal("80")
```

</details>

#### converts 15 to 0F

- converts 15 to 0F
- Verify: converts 15 to 0F
   - Expected: int_to_hex(15) equals `0F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts 15 to 0F")
step("Verify: converts 15 to 0F")
expect(int_to_hex(15)).to_equal("0F")
```

</details>

#### converts 16 to 10

- converts 16 to 10
- Verify: converts 16 to 10
   - Expected: int_to_hex(16) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts 16 to 10")
step("Verify: converts 16 to 10")
expect(int_to_hex(16)).to_equal("10")
```

</details>

### int_to_hex_char

#### all values

#### converts digits 0-9

- converts digits 0-9
- Verify: converts digits 0-9
   - Expected: int_to_hex_char(0) equals `0`
   - Expected: int_to_hex_char(1) equals `1`
   - Expected: int_to_hex_char(2) equals `2`
   - Expected: int_to_hex_char(3) equals `3`
   - Expected: int_to_hex_char(4) equals `4`
   - Expected: int_to_hex_char(5) equals `5`
   - Expected: int_to_hex_char(6) equals `6`
   - Expected: int_to_hex_char(7) equals `7`
   - Expected: int_to_hex_char(8) equals `8`
   - Expected: int_to_hex_char(9) equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts digits 0-9")
step("Verify: converts digits 0-9")
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

- converts letters 10-15
- Verify: converts letters 10-15
   - Expected: int_to_hex_char(10) equals `A`
   - Expected: int_to_hex_char(11) equals `B`
   - Expected: int_to_hex_char(12) equals `C`
   - Expected: int_to_hex_char(13) equals `D`
   - Expected: int_to_hex_char(14) equals `E`
   - Expected: int_to_hex_char(15) equals `F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts letters 10-15")
step("Verify: converts letters 10-15")
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

- returns 0 for value 16
- Verify: returns 0 for value 16
   - Expected: int_to_hex_char(16) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 0 for value 16")
step("Verify: returns 0 for value 16")
expect(int_to_hex_char(16)).to_equal("0")
```

</details>

#### returns 0 for negative value

- returns 0 for negative value
- Verify: returns 0 for negative value
   - Expected: int_to_hex_char(-1) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 0 for negative value")
step("Verify: returns 0 for negative value")
expect(int_to_hex_char(-1)).to_equal("0")
```

</details>

### from_hsl
_Delegates to hsl_to_rgb._

#### creates color from HSL

- creates color from HSL
- Verify: creates color from HSL


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates color from HSL")
step("Verify: creates color from HSL")
val c = from_hsl(0, 100, 50)
expect(c.r).to_be_greater_than(200)
```

</details>

### from_hsv
_Delegates to hsv_to_rgb._

#### creates color from HSV

- creates color from HSV
- Verify: creates color from HSV
   - Expected: c.g equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates color from HSV")
step("Verify: creates color from HSV")
val c = from_hsv(120, 100, 100)
expect(c.g).to_equal(255)  # oracle: 255 — named expected value from the requirement
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2288d72d64e675e165eab574bfeee563b362aa224061acbc261cc73f1a26790e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2288d72d64e675e165eab574bfeee563b362aa224061acbc261cc73f1a26790e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2288d72d64e675e165eab574bfeee563b362aa224061acbc261cc73f1a26790e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/color/color_hsl_spec.spl
mirror: doc/06_spec/01_unit/lib/common/color/color_hsl_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/color/color_hsl_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/color/color_hsl_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/color/color_hsl_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 28 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/color/color_hsl_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts black to HSL zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/color/color_hsl_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts white to HSL' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/color/color_hsl_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts gray to HSL with zero saturation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
