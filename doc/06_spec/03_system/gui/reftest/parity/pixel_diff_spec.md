# Pixel Diff Specification

> <details>

<!-- sdn-diagram:id=pixel_diff_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pixel_diff_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pixel_diff_spec -> std
pixel_diff_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pixel_diff_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pixel Diff Specification

## Scenarios

### compare_pictures

#### two empty pictures have ratio 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _empty_picture()
val b = _empty_picture()
val result = compare_pictures(a, b, _cull_10x10(), 0)
expect result.ratio to_equal 0.0
```

</details>

#### identical pictures (same DrawRect color) have ratio 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _picture_with_rect(255, 0, 0)
val b = _picture_with_rect(255, 0, 0)
val result = compare_pictures(a, b, _cull_10x10(), 0)
expect result.ratio to_equal 0.0
```

</details>

#### different pictures (different rect colors) have ratio > 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _picture_with_rect(255, 0, 0)
val b = _picture_with_rect(0, 0, 255)
val result = compare_pictures(a, b, _cull_10x10(), 0)
expect result.ratio to_be_greater_than 0.0
```

</details>

#### max_delta reports channel difference magnitude for two-color pictures

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _picture_with_rect(255, 0, 0)
val b = _picture_with_rect(0, 0, 0)
val result = compare_pictures(a, b, _cull_10x10(), 0)
expect result.max_delta to_be_greater_than 0
```

</details>

### compare_with_threshold

#### passes when ratio <= threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _empty_picture()
val b = _empty_picture()
val result = compare_with_threshold(a, b, _cull_10x10(), 0.01, 0)
expect result.passed to_equal true
```

</details>

#### fails when ratio > threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _picture_with_rect(255, 0, 0)
val b = _picture_with_rect(0, 0, 255)
val result = compare_with_threshold(a, b, _cull_10x10(), 0.0, 0)
expect result.passed to_equal false
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/reftest/parity/pixel_diff_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- compare_pictures
- compare_with_threshold

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
