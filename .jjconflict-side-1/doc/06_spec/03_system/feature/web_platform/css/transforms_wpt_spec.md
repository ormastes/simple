# Transforms Wpt Specification

> 1. "div { width: 4px; height: 4px; background-color: #dc2626; transform: translate

<!-- sdn-diagram:id=transforms_wpt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=transforms_wpt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

transforms_wpt_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=transforms_wpt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Transforms Wpt Specification

## Scenarios

### WPT-derived CSS transforms subset

#### CSS transform property

#### translate moves element

1. "div { width: 4px; height: 4px; background-color: #dc2626; transform: translate
   - Expected: _pixel_at(pixels, 0, 0) equals `0xFFFFFFFFu32`
   - Expected: _pixel_at(pixels, 4, 4) equals `0xFFDC2626u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = _render(
    "div { width: 4px; height: 4px; background-color: #dc2626; transform: translate(4px, 4px); }",
    "<div></div>")
expect(_pixel_at(pixels, 0, 0)).to_equal(0xFFFFFFFFu32)
expect(_pixel_at(pixels, 4, 4)).to_equal(0xFFDC2626u32)
```

</details>

#### translateX moves element on the inline axis

1. "div { width: 4px; height: 4px; background-color: #16a34a; transform: translateX
   - Expected: _pixel_at(pixels, 0, 0) equals `0xFFFFFFFFu32`
   - Expected: _pixel_at(pixels, 5, 0) equals `0xFF16A34Au32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = _render(
    "div { width: 4px; height: 4px; background-color: #16a34a; transform: translateX(5px); }",
    "<div></div>")
expect(_pixel_at(pixels, 0, 0)).to_equal(0xFFFFFFFFu32)
expect(_pixel_at(pixels, 5, 0)).to_equal(0xFF16A34Au32)
```

</details>

#### translateY moves element on the block axis

1. "div { width: 4px; height: 4px; background-color: #2563eb; transform: translateY
   - Expected: _pixel_at(pixels, 0, 0) equals `0xFFFFFFFFu32`
   - Expected: _pixel_at(pixels, 0, 5) equals `0xFF2563EBu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = _render(
    "div { width: 4px; height: 4px; background-color: #2563eb; transform: translateY(5px); }",
    "<div></div>")
expect(_pixel_at(pixels, 0, 0)).to_equal(0xFFFFFFFFu32)
expect(_pixel_at(pixels, 0, 5)).to_equal(0xFF2563EBu32)
```

</details>

#### percentage translate uses element dimensions

1. "div { width: 10px; height: 8px; background-color: #ea580c; transform: translate
   - Expected: _pixel_at(pixels, 0, 0) equals `0xFFFFFFFFu32`
   - Expected: _pixel_at(pixels, 5, 2) equals `0xFFEA580Cu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = _render(
    "div { width: 10px; height: 8px; background-color: #ea580c; transform: translate(50%, 25%); }",
    "<div></div>")
expect(_pixel_at(pixels, 0, 0)).to_equal(0xFFFFFFFFu32)
expect(_pixel_at(pixels, 5, 2)).to_equal(0xFFEA580Cu32)
```

</details>

#### space-separated percentage translate uses element dimensions

1. "div { width: 10px; height: 8px; background-color: #0f766e; transform: translate
   - Expected: _pixel_at(pixels, 0, 0) equals `0xFFFFFFFFu32`
   - Expected: _pixel_at(pixels, 5, 2) equals `0xFF0F766Eu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = _render(
    "div { width: 10px; height: 8px; background-color: #0f766e; transform: translate(50% 25%); }",
    "<div></div>")
expect(_pixel_at(pixels, 0, 0)).to_equal(0xFFFFFFFFu32)
expect(_pixel_at(pixels, 5, 2)).to_equal(0xFF0F766Eu32)
```

</details>

#### percentage translateX uses element width

1. "div { width: 10px; height: 4px; background-color: #7c3aed; transform: translateX
   - Expected: _pixel_at(pixels, 0, 0) equals `0xFFFFFFFFu32`
   - Expected: _pixel_at(pixels, 5, 0) equals `0xFF7C3AEDu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = _render(
    "div { width: 10px; height: 4px; background-color: #7c3aed; transform: translateX(50%); }",
    "<div></div>")
expect(_pixel_at(pixels, 0, 0)).to_equal(0xFFFFFFFFu32)
expect(_pixel_at(pixels, 5, 0)).to_equal(0xFF7C3AEDu32)
```

</details>

#### percentage translateY uses element height

1. "div { width: 4px; height: 8px; background-color: #0891b2; transform: translateY
   - Expected: _pixel_at(pixels, 0, 0) equals `0xFFFFFFFFu32`
   - Expected: _pixel_at(pixels, 0, 2) equals `0xFF0891B2u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = _render(
    "div { width: 4px; height: 8px; background-color: #0891b2; transform: translateY(25%); }",
    "<div></div>")
expect(_pixel_at(pixels, 0, 0)).to_equal(0xFFFFFFFFu32)
expect(_pixel_at(pixels, 0, 2)).to_equal(0xFF0891B2u32)
```

</details>

#### scale(2) keeps transformed color visible

1. "div { width: 6px; height: 4px; background-color: #16a34a; transform: scale
   - Expected: no_scale > 0 is true
   - Expected: with_scale >= no_scale is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val no_scale = _pixel_count(
    "div { width: 6px; height: 4px; background-color: #16a34a; }",
    "<div></div>",
    0xFF16A34Au32)
val with_scale = _pixel_count(
    "div { width: 6px; height: 4px; background-color: #16a34a; transform: scale(2); }",
    "<div></div>",
    0xFF16A34Au32)
expect(no_scale > 0).to_equal(true)
expect(with_scale >= no_scale).to_equal(true)
```

</details>

#### rotate(0deg) keeps transformed color visible

1. "div { width: 12px; height: 8px; background-color: #7c3aed; transform: rotate
   - Expected: no_rotate > 0 is true
   - Expected: with_rotate > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val no_rotate = _pixel_count(
    "div { width: 12px; height: 8px; background-color: #7c3aed; }",
    "<div></div>",
    0xFF7C3AEDu32)
val with_rotate = _pixel_count(
    "div { width: 12px; height: 8px; background-color: #7c3aed; transform: rotate(0deg); }",
    "<div></div>",
    0xFF7C3AEDu32)
expect(no_rotate > 0).to_equal(true)
expect(with_rotate > 0).to_equal(true)
```

</details>

#### transform-origin keeps rotated color visible

1. "div { width: 8px; height: 8px; background-color: #0891b2; transform: rotate
2. "div { width: 8px; height: 8px; background-color: #0891b2; transform: rotate
   - Expected: center_origin is true
   - Expected: corner_origin is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val center_origin = _renders_color(
    "div { width: 8px; height: 8px; background-color: #0891b2; transform: rotate(45deg); transform-origin: 50% 50%; }",
    "<div></div>",
    0xFF0891B2u32)
val corner_origin = _renders_color(
    "div { width: 8px; height: 8px; background-color: #0891b2; transform: rotate(45deg); transform-origin: 0% 0%; }",
    "<div></div>",
    0xFF0891B2u32)
expect(center_origin).to_equal(true)
expect(corner_origin).to_equal(true)
```

</details>

#### multiple transforms keep composed color visible

1. "div { width: 8px; height: 6px; background-color: #ea580c; transform: translate
   - Expected: composed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val composed = _renders_color(
    "div { width: 8px; height: 6px; background-color: #ea580c; transform: translate(2px, 0px) scale(1.5); }",
    "<div></div>",
    0xFFEA580Cu32)
expect(composed).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/transforms_wpt_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WPT-derived CSS transforms subset

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
