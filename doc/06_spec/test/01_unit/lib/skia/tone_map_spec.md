# Skia Tone Map Specification

> Tests for transfer-function encode/decode pairs (sRGB, gamma 2.2, PQ, HLG), the TransferDirection enum + apply_transfer_fn dispatch, and the rgb_to_rgb linear-space conversion in std.skia.feature.color_management.tone_map.

<!-- sdn-diagram:id=tone_map_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tone_map_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tone_map_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tone_map_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Tone Map Specification

Tests for transfer-function encode/decode pairs (sRGB, gamma 2.2, PQ, HLG), the TransferDirection enum + apply_transfer_fn dispatch, and the rgb_to_rgb linear-space conversion in std.skia.feature.color_management.tone_map.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-012 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/tone_map_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for transfer-function encode/decode pairs (sRGB, gamma 2.2, PQ, HLG),
the TransferDirection enum + apply_transfer_fn dispatch, and the rgb_to_rgb
linear-space conversion in std.skia.feature.color_management.tone_map.

## Scenarios

### tone_map transfer functions

#### srgb_decode maps 0.0 to 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = srgb_decode(0.0)
expect(out).to_equal(0.0)
```

</details>

#### srgb_decode maps 1.0 to 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = srgb_decode(1.0)
val close = math_abs(out - 1.0) < 1e-6
expect(close).to_equal(true)
```

</details>

#### srgb_encode is the inverse of srgb_decode at 0.5

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val linear = srgb_decode(0.5)
val round = srgb_encode(linear)
val close = math_abs(round - 0.5) < 1e-4
expect(close).to_equal(true)
```

</details>

#### pq_decode is the inverse of pq_encode at 0.3

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = pq_encode(0.3)
val round = pq_decode(encoded)
val close = math_abs(round - 0.3) < 1e-3
expect(close).to_equal(true)
```

</details>

#### hlg_decode(0.25) is in the open interval (0, 0.25)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = hlg_decode(0.25)
expect(out).to_be_greater_than(0.0)
expect(out).to_be_less_than(0.25)
```

</details>

### apply_transfer_fn dispatch

#### decode then encode with SkTransferFn.Srgb is identity on 0.42

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0.42
val lin = apply_transfer_fn(SkTransferFn.Srgb, x, TransferDirection.Decode)
val back = apply_transfer_fn(SkTransferFn.Srgb, lin, TransferDirection.Encode)
val close = math_abs(back - x) < 1e-4
expect(close).to_equal(true)
```

</details>

### rgb_to_rgb identity for matching spaces

#### rgb_to_rgb with src == dst == sRGB returns the input color unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cs = srgb()
val input = SkColor4f(r: 0.2, g: 0.4, b: 0.6, a: 0.9)
val out = rgb_to_rgb(input, cs, cs)
expect(out.r).to_equal(0.2)
expect(out.g).to_equal(0.4)
expect(out.b).to_equal(0.6)
expect(out.a).to_equal(0.9)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
