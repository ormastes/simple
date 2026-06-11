# Skia TextBlob V2 Specification

> Tests for SkTextBlobBuilder / SkTextBlobV2 / TextRun / TextRunPositioning — the additive builder-style text blob API in textblob_v2.spl. Legacy SkTextBlob + SkGlyphRun in textblob.spl are left untouched.

<!-- sdn-diagram:id=textblob_v2_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=textblob_v2_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

textblob_v2_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=textblob_v2_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia TextBlob V2 Specification

Tests for SkTextBlobBuilder / SkTextBlobV2 / TextRun / TextRunPositioning — the additive builder-style text blob API in textblob_v2.spl. Legacy SkTextBlob + SkGlyphRun in textblob.spl are left untouched.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-TEXTBLOB-V2 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/textblob_v2_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for SkTextBlobBuilder / SkTextBlobV2 / TextRun / TextRunPositioning —
the additive builder-style text blob API in textblob_v2.spl. Legacy
SkTextBlob + SkGlyphRun in textblob.spl are left untouched.

## Scenarios

### textblob_v2

#### builder: new has zero runs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = sk_text_blob_builder_new()
expect(b.run_count()).to_equal(0)
```

</details>

#### builder: add_run_default appends a run

1. b add run default
   - Expected: b.run_count() equals `1`
   - Expected: r.glyphs.len() equals `3`
   - Expected: r.origin_x equals `5.0`
   - Expected: r.origin_y equals `7.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = sk_text_blob_builder_new()
val f = _mk_font()
b.add_run_default(f, [10, 11, 12], 5.0, 7.0)
expect(b.run_count()).to_equal(1)
val r = b.runs[0]
expect(r.glyphs.len()).to_equal(3)
expect(r.origin_x).to_equal(5.0)
expect(r.origin_y).to_equal(7.0)
```

</details>

#### builder: add_run_horizontal stores per-glyph x-positions

1. b add run horizontal
   - Expected: b.run_count() equals `1`
   - Expected: r.positions.len() equals `3`
   - Expected: r.positions[1] equals `6.0`
   - Expected: r.origin_y equals `4.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = sk_text_blob_builder_new()
val f = _mk_font()
b.add_run_horizontal(f, [1, 2, 3], [0.0, 6.0, 12.0], 4.0)
expect(b.run_count()).to_equal(1)
val r = b.runs[0]
expect(r.positions.len()).to_equal(3)
expect(r.positions[1]).to_equal(6.0)
expect(r.origin_y).to_equal(4.0)
```

</details>

#### build() finalizes, returns SkTextBlobV2 with all runs

1. b add run default
2. b add run horizontal
3. b add run full
   - Expected: blob.run_count() equals `3`
   - Expected: blob.glyph_count() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = sk_text_blob_builder_new()
val f = _mk_font()
b.add_run_default(f, [1, 2], 0.0, 0.0)
b.add_run_horizontal(f, [3, 4], [0.0, 8.0], 10.0)
b.add_run_full(f, [5], [16.0, 10.0])
val blob = b.build()
expect(blob.run_count()).to_equal(3)
expect(blob.glyph_count()).to_equal(5)
```

</details>

#### SkTextBlobV2: bounds field exists and has non-negative width

1. b add run horizontal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = sk_text_blob_builder_new()
val f = _mk_font()
b.add_run_horizontal(f, [1, 2, 3], [0.0, 6.0, 12.0], 4.0)
val blob = b.build()
val width = blob.bounds.right - blob.bounds.left
expect(width).to_be_greater_than(-0.0001)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
