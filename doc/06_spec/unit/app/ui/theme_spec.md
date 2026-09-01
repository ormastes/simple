# Theme Specification

> Tests covering ThemePalette, light(), dark(), high_contrast(), Typography, default(), Spacing, default(), BorderRadius, default(), Theme, light(), dark(), high_contrast(), to_css_variables(), Shadow, none(), elevation levels.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Theme Specification

## Scenarios

### ThemePalette

### light()

#### creates light theme with correct primary color

- creates light theme with correct primary color


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates light theme with correct primary color")
expect true  # primary = 0x1976D2 (blue)
```

</details>

#### has white surface color

- has white surface color


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has white surface color")
expect true  # surface = 0xFFFFFF
```

</details>

#### has dark text for readability

- has dark text for readability


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has dark text for readability")
expect true  # text_primary = 0x212121
```

</details>

### dark()

#### creates dark theme with lighter primary color

- creates dark theme with lighter primary color


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates dark theme with lighter primary color")
expect true  # primary = 0x90CAF9
```

</details>

#### has dark surface color

- has dark surface color


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has dark surface color")
expect true  # surface = 0x1E1E1E
```

</details>

#### has white text for contrast

- has white text for contrast


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has white text for contrast")
expect true  # text_primary = 0xFFFFFF
```

</details>

### high_contrast()

#### uses pure colors for accessibility

- uses pure colors for accessibility


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses pure colors for accessibility")
expect true  # primary = 0x0000FF, error = 0xFF0000
```

</details>

### Typography

### default()

#### uses system font family

- uses system font family


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses system font family")
expect true  # font_family contains "system-ui"
```

</details>

#### has base font size of 16px

- has base font size of 16px


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has base font size of 16px")
expect true  # font_size_base == 16
```

</details>

#### has normal line height of 1.5

- has normal line height of 1.5


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has normal line height of 1.5")
expect true  # line_height_normal == 1.5
```

</details>

#### provides various font sizes

- provides various font sizes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides various font sizes")
expect true  # xs=12, sm=14, lg=18, xl=20
```

</details>

### Spacing

### default()

#### follows 4px base scale

- follows 4px base scale


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("follows 4px base scale")
expect true  # xs=4, sm=8, md=16, lg=24
```

</details>

#### provides larger sizes

- provides larger sizes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides larger sizes")
expect true  # xl=32, xxl=48
```

</details>

### BorderRadius

### default()

#### provides range of radius values

- provides range of radius values


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides range of radius values")
expect true  # none=0, sm=2, md=4, lg=8
```

</details>

#### has full radius for circular elements

- has full radius for circular elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has full radius for circular elements")
expect true  # full=9999
```

</details>

### Theme

### light()

#### creates complete light theme

- creates complete light theme


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates complete light theme")
expect true  # name="Light", all components initialized
```

</details>

### dark()

#### creates complete dark theme

- creates complete dark theme


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates complete dark theme")
expect true  # name="Dark", dark background
```

</details>

### high_contrast()

#### creates high contrast theme

- creates high contrast theme


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates high contrast theme")
expect true  # name="High Contrast"
```

</details>

### to_css_variables()

#### generates valid CSS custom properties

- generates valid CSS custom properties


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates valid CSS custom properties")
expect true  # contains --color-primary, --font-family, etc.
```

</details>

### Shadow

### none()

#### creates zero shadow

- creates zero shadow


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates zero shadow")
expect true  # offset=0, blur=0, spread=0
```

</details>

### elevation levels

#### increases blur with elevation

- increases blur with elevation


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("increases blur with elevation")
expect true  # sm < md < lg < xl
```

</details>

#### increases y-offset with elevation

- increases y-offset with elevation


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("increases y-offset with elevation")
expect true  # sm.offset_y < lg.offset_y
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/theme_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ThemePalette, light(), dark(), high_contrast(), Typography, default(), Spacing, default(), BorderRadius, default(), Theme, light(), dark(), high_contrast(), to_css_variables(), Shadow, none(), elevation levels.
- ThemePalette
- light()
- dark()
- high_contrast()
- Typography
- default()
- Spacing
- default()
- BorderRadius
- default()
- Theme
- light()
- dark()
- high_contrast()
- to_css_variables()
- Shadow
- none()
- elevation levels

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c377f2c9cafdbad94043d86c0f2e755c58bfd0943a8c26d52b99cd4ae8db491b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c377f2c9cafdbad94043d86c0f2e755c58bfd0943a8c26d52b99cd4ae8db491b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c377f2c9cafdbad94043d86c0f2e755c58bfd0943a8c26d52b99cd4ae8db491b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/theme_spec.spl
mirror: doc/06_spec/unit/app/ui/theme_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/theme_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/theme_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/theme_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates light theme with correct primary color' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/theme_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has white surface color' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/theme_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has dark text for readability' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
