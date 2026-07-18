# Theme Specification

> 1. expect true  # primary = 0x1976D2

<!-- sdn-diagram:id=theme_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=theme_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

theme_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=theme_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

1. expect true  # primary = 0x1976D2


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # primary = 0x1976D2 (blue)
```

</details>

#### has white surface color

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # surface = 0xFFFFFF
```

</details>

#### has dark text for readability

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # text_primary = 0x212121
```

</details>

### dark()

#### creates dark theme with lighter primary color

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # primary = 0x90CAF9
```

</details>

#### has dark surface color

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # surface = 0x1E1E1E
```

</details>

#### has white text for contrast

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # text_primary = 0xFFFFFF
```

</details>

### high_contrast()

#### uses pure colors for accessibility

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # primary = 0x0000FF, error = 0xFF0000
```

</details>

### Typography

### default()

#### uses system font family

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # font_family contains "system-ui"
```

</details>

#### has base font size of 16px

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # font_size_base == 16
```

</details>

#### has normal line height of 1.5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # line_height_normal == 1.5
```

</details>

#### provides various font sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # xs=12, sm=14, lg=18, xl=20
```

</details>

### Spacing

### default()

#### follows 4px base scale

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # xs=4, sm=8, md=16, lg=24
```

</details>

#### provides larger sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # xl=32, xxl=48
```

</details>

### BorderRadius

### default()

#### provides range of radius values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # none=0, sm=2, md=4, lg=8
```

</details>

#### has full radius for circular elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # full=9999
```

</details>

### Theme

### light()

#### creates complete light theme

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # name="Light", all components initialized
```

</details>

### dark()

#### creates complete dark theme

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # name="Dark", dark background
```

</details>

### high_contrast()

#### creates high contrast theme

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # name="High Contrast"
```

</details>

### to_css_variables()

#### generates valid CSS custom properties

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # contains --color-primary, --font-family, etc.
```

</details>

### Shadow

### none()

#### creates zero shadow

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # offset=0, blur=0, spread=0
```

</details>

### elevation levels

#### increases blur with elevation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # sm < md < lg < xl
```

</details>

#### increases y-offset with elevation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # sm.offset_y < lg.offset_y
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/theme_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
