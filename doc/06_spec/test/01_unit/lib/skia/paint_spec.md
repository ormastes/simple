# Skia Paint Specification

> Tests for SkPaint construction and builder-style mutation.

<!-- sdn-diagram:id=paint_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=paint_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

paint_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=paint_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Paint Specification

Tests for SkPaint construction and builder-style mutation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-004 |
| Category | Stdlib |
| Difficulty | 1/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/paint_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for SkPaint construction and builder-style mutation.

## Scenarios

### SkPaint construction

#### sk_paint_new default is fill

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_paint_new()
expect(p.style).to_equal(SkPaintStyle.Fill)
```

</details>

#### sk_paint_new default anti_alias is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_paint_new()
expect(p.anti_alias).to_equal(false)
```

</details>

#### sk_paint_new default stroke_width is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_paint_new()
expect(p.stroke_width).to_equal(0.0)
```

</details>

#### sk_paint_new default color is black

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_paint_new()
expect(p.color).to_equal(sk_color_black())
```

</details>

#### sk_paint_fill creates fill paint

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_paint_fill(sk_color_white())
expect(p.style).to_equal(SkPaintStyle.Fill)
expect(p.anti_alias).to_equal(true)
```

</details>

#### sk_paint_stroke creates stroke paint

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_paint_stroke(sk_color_black(), 2.0)
expect(p.style).to_equal(SkPaintStyle.Stroke)
expect(p.stroke_width).to_equal(2.0)
```

</details>

### SkPaint with_ builders

#### with_color changes color

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_paint_new()
val white = sk_color_white()
val p2 = p.with_color(white)
expect(p2.color).to_equal(white)
```

</details>

#### with_style changes style to stroke

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_paint_new()
val p2 = p.with_style(SkPaintStyle.Stroke)
expect(p2.style).to_equal(SkPaintStyle.Stroke)
```

</details>

#### with_stroke_width sets width

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_paint_new()
val p2 = p.with_stroke_width(5.0)
expect(p2.stroke_width).to_equal(5.0)
```

</details>

#### with_anti_alias enables aa

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_paint_new()
val p2 = p.with_anti_alias(true)
expect(p2.anti_alias).to_equal(true)
```

</details>

#### with_blend_mode sets mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_paint_new()
val p2 = p.with_blend_mode(SkBlendMode.Multiply)
expect(p2.blend_mode).to_equal(SkBlendMode.Multiply)
```

</details>

#### builders are immutable — original unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_paint_new()
val _ = p.with_stroke_width(99.0)
expect(p.stroke_width).to_equal(0.0)
```

</details>

### SkPaint predicates

#### is_fill true for fill paint

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_paint_fill(sk_color_black())
expect(p.is_fill()).to_equal(true)
expect(p.is_stroke()).to_equal(false)
```

</details>

#### is_stroke true for stroke paint

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_paint_stroke(sk_color_black(), 1.0)
expect(p.is_stroke()).to_equal(true)
expect(p.is_fill()).to_equal(false)
```

</details>

### SkPaint to_string

#### to_string contains SkPaint

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_paint_new()
expect(p.to_string()).to_contain("SkPaint")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
