# Skia Color Space Specification

> Tests for SkColorSpace named variants, transfer functions, chromaticity primaries, predicate helpers, and RGB→XYZ primary matrix stubs.

<!-- sdn-diagram:id=color_space_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=color_space_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

color_space_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=color_space_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Color Space Specification

Tests for SkColorSpace named variants, transfer functions, chromaticity primaries, predicate helpers, and RGB→XYZ primary matrix stubs.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-010 |
| Category | Stdlib |
| Difficulty | 1/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/color_space_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for SkColorSpace named variants, transfer functions, chromaticity primaries,
predicate helpers, and RGB→XYZ primary matrix stubs.

## Scenarios

### SkColorSpace named constructors

#### srgb() returns kind Srgb with Srgb transfer and D65 white point

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cs = srgb()
expect(cs.kind).to_equal(SkColorSpaceKind.Srgb)
expect(cs.transfer_fn).to_equal(SkTransferFn.Srgb)
val wx_ok = math_abs(cs.chromaticities.white_x - 0.3127) < 1e-5
expect(wx_ok).to_equal(true)
val wy_ok = math_abs(cs.chromaticities.white_y - 0.3290) < 1e-5
expect(wy_ok).to_equal(true)
```

</details>

#### display_p3() returns DisplayP3 kind with D65 white point

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cs = display_p3()
expect(cs.kind).to_equal(SkColorSpaceKind.DisplayP3)
val wx_ok = math_abs(cs.chromaticities.white_x - 0.3127) < 1e-5
expect(wx_ok).to_equal(true)
```

</details>

#### rec2020() returns Rec2020 kind with Pq transfer function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cs = rec2020()
expect(cs.kind).to_equal(SkColorSpaceKind.Rec2020)
expect(cs.transfer_fn).to_equal(SkTransferFn.Pq)
```

</details>

#### sk_color_space_is_srgb returns true for srgb()

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cs = srgb()
val result = sk_color_space_is_srgb(cs)
expect(result).to_equal(true)
```

</details>

#### sk_color_space_is_wide_gamut returns true for display_p3()

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cs = display_p3()
val result = sk_color_space_is_wide_gamut(cs)
expect(result).to_equal(true)
```

</details>

#### sk_color_space_is_wide_gamut returns false for srgb()

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cs = srgb()
val result = sk_color_space_is_wide_gamut(cs)
expect(result).to_equal(false)
```

</details>

#### sk_color_space_is_hdr returns true for rec2020() which uses Pq transfer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cs = rec2020()
val result = sk_color_space_is_hdr(cs)
expect(result).to_equal(true)
```

</details>

<details>
<summary>Advanced: primary_matrix_for srgb has m00 ≈ 0.4124564</summary>

#### primary_matrix_for srgb has m00 ≈ 0.4124564

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cs = srgb()
val m = primary_matrix_for(cs)
val ok = math_abs(m.m00 - 0.4124564) < 1e-5
expect(ok).to_equal(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
