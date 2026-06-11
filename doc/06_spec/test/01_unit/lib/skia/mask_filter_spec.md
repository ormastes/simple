# Skia Mask Filter Specification

> Tests for apply_mask_filter — Skia SkMaskFilter equivalents that operate on the alpha (coverage) channel BEFORE color modulation. Covers Identity, Blur, Emboss and Shadow kinds, plus the mask_filter_blur constructor.

<!-- sdn-diagram:id=mask_filter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mask_filter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mask_filter_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mask_filter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Mask Filter Specification

Tests for apply_mask_filter — Skia SkMaskFilter equivalents that operate on the alpha (coverage) channel BEFORE color modulation. Covers Identity, Blur, Emboss and Shadow kinds, plus the mask_filter_blur constructor.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-MASKFILTER |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/mask_filter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for apply_mask_filter — Skia SkMaskFilter equivalents that operate on
the alpha (coverage) channel BEFORE color modulation. Covers Identity, Blur,
Emboss and Shadow kinds, plus the mask_filter_blur constructor.

## Scenarios

### mask_filter

#### apply_mask_filter: Identity returns input unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _make_disk(8, 8, 2)
val f = mask_filter_identity()
val out = apply_mask_filter(src, f)
expect(out.width).to_equal(8)
expect(out.height).to_equal(8)
# Centre alpha is opaque in source; identity preserves it.
val centre = _alpha_at(out, 4, 4)
expect(centre).to_equal(255)
# Corner is empty; identity preserves it.
val corner = _alpha_at(out, 0, 0)
expect(corner).to_equal(0)
```

</details>

#### apply_mask_filter: Blur produces output with roughly the same bounds but softer edges

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _make_disk(16, 16, 3)
val f = mask_filter_blur(2.0)
val out = apply_mask_filter(src, f)
# Bounds preserved.
expect(out.width).to_equal(16)
expect(out.height).to_equal(16)
# Centre stays bright but may dim a touch from box-blur normalisation.
val centre = _alpha_at(out, 8, 8)
expect(centre).to_be_greater_than(100)
# An outside pixel that was 0 should now have non-zero alpha (softened edge).
val edge = _alpha_at(out, 8, 12)
expect(edge).to_be_greater_than(0)
# And it should still be less than the centre (true blur falloff).
expect(edge).to_be_less_than(centre + 1)
```

</details>

#### apply_mask_filter: Emboss produces output with gradient-driven intensity

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _make_disk(16, 16, 4)
# Light direction roughly (+x, +y): pixels on the +x/+y rim should be
# brighter than 0.5*255 (~128); pixels on the -x/-y rim should be
# darker than 128.
val f = mask_filter_emboss(1.0, 1.0)
val out = apply_mask_filter(src, f)
expect(out.width).to_equal(16)
expect(out.height).to_equal(16)
# Interior of disk: gradient is ~0, so alpha ≈ 128.
val interior = _alpha_at(out, 8, 8)
val interior_near_mid = interior >= 120 and interior <= 136
expect(interior_near_mid).to_equal(true)
# Far outside disk: gradient also 0 → ~128 (flat background).
val far = _alpha_at(out, 0, 0)
val far_near_mid = far >= 120 and far <= 136
expect(far_near_mid).to_equal(true)
```

</details>

#### apply_mask_filter: Shadow produces an offset blurred copy

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _make_disk(16, 16, 3)
val f = mask_filter_shadow(4.0, 4.0, 1.5)
val out = apply_mask_filter(src, f)
# Output bitmap is padded by the shadow offset.
expect(out.width).to_equal(20)
expect(out.height).to_equal(20)
# Original disk centre was at (8,8); shifted by (+4,+4) → (12,12).
val shifted_centre = _alpha_at(out, 12, 12)
expect(shifted_centre).to_be_greater_than(0)
# The original centre location should be much dimmer (shadow moved away).
val original_centre = _alpha_at(out, 8, 8)
expect(original_centre).to_be_less_than(shifted_centre + 1)
```

</details>

#### mask_filter_blur: constructor stores sigma

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = mask_filter_blur(3.5)
expect(f.blur_sigma).to_equal(3.5)
# Negative sigmas clamp to zero.
val f2 = mask_filter_blur(0.0 - 2.0)
expect(f2.blur_sigma).to_equal(0.0)
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
