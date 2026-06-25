# Color Utils Specification

> <details>

<!-- sdn-diagram:id=color_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=color_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

color_utils_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=color_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Color Utils Specification

## Scenarios

### Color Utils

#### keeps common color constructors available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/lib/common/color/types.spl") ?? ""

expect(source).to_contain("pub fn from_rgba(r: i64, g: i64, b: i64, a: i64) -> Color")
expect(source).to_contain("pub fn from_rgb(r: i64, g: i64, b: i64) -> Color")
expect(source).to_contain("pub fn black() -> Color")
expect(source).to_contain("pub fn white() -> Color")
```

</details>

#### keeps common color utility operations available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/lib/common/color/utilities.spl") ?? ""

expect(source).to_contain("pub fn luminance(color: Color) -> i64")
expect(source).to_contain("pub fn contrast_ratio(c1: Color, c2: Color) -> i64")
expect(source).to_contain("pub fn is_accessible(fg: Color, bg: Color, level: text) -> bool")
expect(source).to_contain("pub fn web_safe(color: Color) -> Color")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/color_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Color Utils

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
