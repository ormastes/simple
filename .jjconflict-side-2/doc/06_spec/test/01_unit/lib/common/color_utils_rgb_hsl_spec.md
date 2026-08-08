# Color Utils Rgb Hsl Specification

> <details>

<!-- sdn-diagram:id=color_utils_rgb_hsl_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=color_utils_rgb_hsl_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

color_utils_rgb_hsl_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=color_utils_rgb_hsl_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Color Utils Rgb Hsl Specification

## Scenarios

### Color Utils Ext

#### keeps RGB, hex, HSL, and HSV conversion entrypoints available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = color_convert_source()

expect(source).to_contain("pub fn from_hex(value: text) -> Color")
expect(source).to_contain("pub fn to_hex(color: Color) -> text")
expect(source).to_contain("pub fn rgb_to_hsl(color: Color)")
expect(source).to_contain("pub fn hsl_to_rgb(h: i64, s: i64, l: i64) -> Color")
expect(source).to_contain("pub fn hsv_to_rgb(h: i64, s: i64, v: i64) -> Color")
```

</details>

#### keeps color manipulation helpers alpha-preserving where needed

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = color_manipulate_source()

expect(source).to_contain("pub fn lighten(color: Color, amount: i64) -> Color")
expect(source).to_contain("pub fn darken(color: Color, amount: i64) -> Color")
expect(source).to_contain("pub fn saturate(color: Color, amount: i64) -> Color")
expect(source).to_contain("pub fn desaturate(color: Color, amount: i64) -> Color")
expect(source).to_contain("pub fn set_alpha(color: Color, alpha: i64) -> Color")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/color_utils_rgb_hsl_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Color Utils Ext

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
