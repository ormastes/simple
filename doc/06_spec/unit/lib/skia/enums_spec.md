# Skia Enums Specification

> Tests that all Skia enum variants construct correctly and compare by identity.

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
| Source | `test/unit/lib/skia/enums_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that all Skia enum variants construct correctly and compare by identity.

## Scenarios

### SkPaintStyle

#### Fill variant exists

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Fill variant exists
   - Expected: s equals `SkPaintStyle.Fill`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Fill variant exists")
val s = SkPaintStyle.Fill
expect(s).to_equal(SkPaintStyle.Fill)
```

</details>

#### Stroke variant exists

- Stroke variant exists
   - Expected: s equals `SkPaintStyle.Stroke`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Stroke variant exists")
val s = SkPaintStyle.Stroke
expect(s).to_equal(SkPaintStyle.Stroke)
```

</details>

#### StrokeAndFill variant exists

- StrokeAndFill variant exists
   - Expected: s equals `SkPaintStyle.StrokeAndFill`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("StrokeAndFill variant exists")
val s = SkPaintStyle.StrokeAndFill
expect(s).to_equal(SkPaintStyle.StrokeAndFill)
```

</details>

#### Fill != Stroke

- Fill != Stroke


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Fill != Stroke")
expect(SkPaintStyle.Fill).to_not_equal(SkPaintStyle.Stroke)
```

</details>

### SkPaintCap

#### Butt variant

- Butt variant
   - Expected: SkPaintCap.Butt equals `SkPaintCap.Butt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Butt variant")
expect(SkPaintCap.Butt).to_equal(SkPaintCap.Butt)
```

</details>

#### Round variant

- Round variant
   - Expected: SkPaintCap.Round equals `SkPaintCap.Round`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Round variant")
expect(SkPaintCap.Round).to_equal(SkPaintCap.Round)
```

</details>

#### Square variant

- Square variant
   - Expected: SkPaintCap.Square equals `SkPaintCap.Square`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Square variant")
expect(SkPaintCap.Square).to_equal(SkPaintCap.Square)
```

</details>

### SkPaintJoin

#### Miter variant

- Miter variant
   - Expected: SkPaintJoin.Miter equals `SkPaintJoin.Miter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Miter variant")
expect(SkPaintJoin.Miter).to_equal(SkPaintJoin.Miter)
```

</details>

#### Round variant

- Round variant
   - Expected: SkPaintJoin.Round equals `SkPaintJoin.Round`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Round variant")
expect(SkPaintJoin.Round).to_equal(SkPaintJoin.Round)
```

</details>

#### Bevel variant

- Bevel variant
   - Expected: SkPaintJoin.Bevel equals `SkPaintJoin.Bevel`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Bevel variant")
expect(SkPaintJoin.Bevel).to_equal(SkPaintJoin.Bevel)
```

</details>

### SkBlendMode

#### SrcOver is default blend mode

- SrcOver is default blend mode
   - Expected: bm equals `SkBlendMode.SrcOver`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SrcOver is default blend mode")
val bm = SkBlendMode.SrcOver
expect(bm).to_equal(SkBlendMode.SrcOver)
```

</details>

#### Clear variant exists

- Clear variant exists
   - Expected: SkBlendMode.Clear equals `SkBlendMode.Clear`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Clear variant exists")
expect(SkBlendMode.Clear).to_equal(SkBlendMode.Clear)
```

</details>

#### Multiply variant exists

- Multiply variant exists
   - Expected: SkBlendMode.Multiply equals `SkBlendMode.Multiply`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Multiply variant exists")
expect(SkBlendMode.Multiply).to_equal(SkBlendMode.Multiply)
```

</details>

#### SrcOver != Dst

- SrcOver != Dst


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SrcOver != Dst")
expect(SkBlendMode.SrcOver).to_not_equal(SkBlendMode.Dst)
```

</details>

### SkPathFillType

#### Winding variant

- Winding variant
   - Expected: SkPathFillType.Winding equals `SkPathFillType.Winding`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Winding variant")
expect(SkPathFillType.Winding).to_equal(SkPathFillType.Winding)
```

</details>

#### EvenOdd variant

- EvenOdd variant
   - Expected: SkPathFillType.EvenOdd equals `SkPathFillType.EvenOdd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EvenOdd variant")
expect(SkPathFillType.EvenOdd).to_equal(SkPathFillType.EvenOdd)
```

</details>

#### InverseWinding variant

- InverseWinding variant
   - Expected: SkPathFillType.InverseWinding equals `SkPathFillType.InverseWinding`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("InverseWinding variant")
expect(SkPathFillType.InverseWinding).to_equal(SkPathFillType.InverseWinding)
```

</details>

#### InverseEvenOdd variant

- InverseEvenOdd variant
   - Expected: SkPathFillType.InverseEvenOdd equals `SkPathFillType.InverseEvenOdd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("InverseEvenOdd variant")
expect(SkPathFillType.InverseEvenOdd).to_equal(SkPathFillType.InverseEvenOdd)
```

</details>

### SkPathDirection

#### Cw variant

- Cw variant
   - Expected: SkPathDirection.Cw equals `SkPathDirection.Cw`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Cw variant")
expect(SkPathDirection.Cw).to_equal(SkPathDirection.Cw)
```

</details>

#### Ccw variant

- Ccw variant
   - Expected: SkPathDirection.Ccw equals `SkPathDirection.Ccw`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Ccw variant")
expect(SkPathDirection.Ccw).to_equal(SkPathDirection.Ccw)
```

</details>

### SkClipOp

#### Difference variant

- Difference variant
   - Expected: SkClipOp.Difference equals `SkClipOp.Difference`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Difference variant")
expect(SkClipOp.Difference).to_equal(SkClipOp.Difference)
```

</details>

#### Intersect variant

- Intersect variant
   - Expected: SkClipOp.Intersect equals `SkClipOp.Intersect`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Intersect variant")
expect(SkClipOp.Intersect).to_equal(SkClipOp.Intersect)
```

</details>

### SkTileMode

#### Clamp variant

- Clamp variant
   - Expected: SkTileMode.Clamp equals `SkTileMode.Clamp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Clamp variant")
expect(SkTileMode.Clamp).to_equal(SkTileMode.Clamp)
```

</details>

#### Repeat variant

- Repeat variant
   - Expected: SkTileMode.Repeat equals `SkTileMode.Repeat`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Repeat variant")
expect(SkTileMode.Repeat).to_equal(SkTileMode.Repeat)
```

</details>

#### Mirror variant

- Mirror variant
   - Expected: SkTileMode.Mirror equals `SkTileMode.Mirror`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Mirror variant")
expect(SkTileMode.Mirror).to_equal(SkTileMode.Mirror)
```

</details>

#### Decal variant

- Decal variant
   - Expected: SkTileMode.Decal equals `SkTileMode.Decal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Decal variant")
expect(SkTileMode.Decal).to_equal(SkTileMode.Decal)
```

</details>

### SkAlphaType

#### Premul variant

- Premul variant
   - Expected: SkAlphaType.Premul equals `SkAlphaType.Premul`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Premul variant")
expect(SkAlphaType.Premul).to_equal(SkAlphaType.Premul)
```

</details>

#### Opaque variant

- Opaque variant
   - Expected: SkAlphaType.Opaque equals `SkAlphaType.Opaque`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Opaque variant")
expect(SkAlphaType.Opaque).to_equal(SkAlphaType.Opaque)
```

</details>

### SkColorType

#### Rgba8888 variant

- Rgba8888 variant
   - Expected: SkColorType.Rgba8888 equals `SkColorType.Rgba8888`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Rgba8888 variant")
expect(SkColorType.Rgba8888).to_equal(SkColorType.Rgba8888)
```

</details>

#### Alpha8 variant

- Alpha8 variant
   - Expected: SkColorType.Alpha8 equals `SkColorType.Alpha8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Alpha8 variant")
expect(SkColorType.Alpha8).to_equal(SkColorType.Alpha8)
```

</details>

### SkTextEncoding

#### Utf8 variant

- Utf8 variant
   - Expected: SkTextEncoding.Utf8 equals `SkTextEncoding.Utf8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Utf8 variant")
expect(SkTextEncoding.Utf8).to_equal(SkTextEncoding.Utf8)
```

</details>

#### GlyphId variant

- GlyphId variant
   - Expected: SkTextEncoding.GlyphId equals `SkTextEncoding.GlyphId`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GlyphId variant")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2a21cd795003e742ca56d653736e39ed2e8cd837fe813e9bb9baca1457fe0397`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2a21cd795003e742ca56d653736e39ed2e8cd837fe813e9bb9baca1457fe0397`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2a21cd795003e742ca56d653736e39ed2e8cd837fe813e9bb9baca1457fe0397`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/skia/enums_spec.spl
mirror: doc/06_spec/unit/lib/skia/enums_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/skia/enums_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/skia/enums_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/skia/enums_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Fill variant exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/skia/enums_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Stroke variant exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/skia/enums_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'StrokeAndFill variant exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
