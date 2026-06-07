# Skia Enums Specification

> Tests that all Skia enum variants construct correctly and compare by identity.

<!-- sdn-diagram:id=enums_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=enums_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

enums_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=enums_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Enums Specification

Tests that all Skia enum variants construct correctly and compare by identity.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-001 |
| Category | Stdlib |
| Difficulty | 1/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/enums_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that all Skia enum variants construct correctly and compare by identity.

## Scenarios

### SkPaintStyle

#### Fill variant exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = SkPaintStyle.Fill
expect(s).to_equal(SkPaintStyle.Fill)
```

</details>

#### Stroke variant exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = SkPaintStyle.Stroke
expect(s).to_equal(SkPaintStyle.Stroke)
```

</details>

#### StrokeAndFill variant exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = SkPaintStyle.StrokeAndFill
expect(s).to_equal(SkPaintStyle.StrokeAndFill)
```

</details>

#### Fill != Stroke

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkPaintStyle.Fill == SkPaintStyle.Stroke).to_equal(false)
```

</details>

### SkPaintCap

#### Butt variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkPaintCap.Butt).to_equal(SkPaintCap.Butt)
```

</details>

#### Round variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkPaintCap.Round).to_equal(SkPaintCap.Round)
```

</details>

#### Square variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkPaintCap.Square).to_equal(SkPaintCap.Square)
```

</details>

### SkPaintJoin

#### Miter variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkPaintJoin.Miter).to_equal(SkPaintJoin.Miter)
```

</details>

#### Round variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkPaintJoin.Round).to_equal(SkPaintJoin.Round)
```

</details>

#### Bevel variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkPaintJoin.Bevel).to_equal(SkPaintJoin.Bevel)
```

</details>

### SkBlendMode

#### SrcOver is default blend mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bm = SkBlendMode.SrcOver
expect(bm).to_equal(SkBlendMode.SrcOver)
```

</details>

#### Clear variant exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkBlendMode.Clear).to_equal(SkBlendMode.Clear)
```

</details>

#### Multiply variant exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkBlendMode.Multiply).to_equal(SkBlendMode.Multiply)
```

</details>

#### SrcOver != Dst

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkBlendMode.SrcOver == SkBlendMode.Dst).to_equal(false)
```

</details>

### SkPathFillType

#### Winding variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkPathFillType.Winding).to_equal(SkPathFillType.Winding)
```

</details>

#### EvenOdd variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkPathFillType.EvenOdd).to_equal(SkPathFillType.EvenOdd)
```

</details>

#### InverseWinding variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkPathFillType.InverseWinding).to_equal(SkPathFillType.InverseWinding)
```

</details>

#### InverseEvenOdd variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkPathFillType.InverseEvenOdd).to_equal(SkPathFillType.InverseEvenOdd)
```

</details>

### SkPathDirection

#### Cw variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkPathDirection.Cw).to_equal(SkPathDirection.Cw)
```

</details>

#### Ccw variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkPathDirection.Ccw).to_equal(SkPathDirection.Ccw)
```

</details>

### SkClipOp

#### Difference variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkClipOp.Difference).to_equal(SkClipOp.Difference)
```

</details>

#### Intersect variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkClipOp.Intersect).to_equal(SkClipOp.Intersect)
```

</details>

### SkTileMode

#### Clamp variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkTileMode.Clamp).to_equal(SkTileMode.Clamp)
```

</details>

#### Repeat variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkTileMode.Repeat).to_equal(SkTileMode.Repeat)
```

</details>

#### Mirror variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkTileMode.Mirror).to_equal(SkTileMode.Mirror)
```

</details>

#### Decal variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkTileMode.Decal).to_equal(SkTileMode.Decal)
```

</details>

### SkAlphaType

#### Premul variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkAlphaType.Premul).to_equal(SkAlphaType.Premul)
```

</details>

#### Opaque variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkAlphaType.Opaque).to_equal(SkAlphaType.Opaque)
```

</details>

### SkColorType

#### Rgba8888 variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkColorType.Rgba8888).to_equal(SkColorType.Rgba8888)
```

</details>

#### Alpha8 variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkColorType.Alpha8).to_equal(SkColorType.Alpha8)
```

</details>

### SkTextEncoding

#### Utf8 variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkTextEncoding.Utf8).to_equal(SkTextEncoding.Utf8)
```

</details>

#### GlyphId variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SkTextEncoding.GlyphId).to_equal(SkTextEncoding.GlyphId)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
