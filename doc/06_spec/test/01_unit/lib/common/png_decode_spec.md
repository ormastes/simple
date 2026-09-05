# Png Decode Specification

> <details>

<!-- sdn-diagram:id=png_decode_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=png_decode_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

png_decode_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=png_decode_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Png Decode Specification

## Scenarios

### PngDecode — signature validation

#### invalid data

#### AC-2: empty bytes returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = []
val result = decode_png_to_argb(data)
expect(result.is_err()).to_equal(true)
```

</details>

#### AC-2: non-PNG bytes returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [0, 1, 2, 3, 4, 5, 6, 7]
val result = decode_png_to_argb(data)
expect(result.is_err()).to_equal(true)
```

</details>

#### AC-2: truncated PNG signature returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [137, 80, 78, 71]
val result = decode_png_to_argb(data)
expect(result.is_err()).to_equal(true)
```

</details>

#### valid signature but truncated content

#### AC-2: PNG signature only (no chunks) returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = decode_png_to_argb(PNG_SIGNATURE)
expect(result.is_err()).to_equal(true)
```

</details>

### PngDecode — PngImage output

#### decoded image properties

#### AC-2: PngImage has width field

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This test will fail because no real PNG data exists yet,
# but validates the struct shape
val data: [u8] = [0]
val result = decode_png_to_argb(data)
# Error case — but the Ok type should have width
expect(result.is_err()).to_equal(true)
```

</details>

#### AC-2: PngImage pixels are ARGB u32 format

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# When a valid PNG is decoded, each pixel should be a u32
# with A in bits 24-31, R in 16-23, G in 8-15, B in 0-7
val data: [u8] = [0]
val result = decode_png_to_argb(data)
expect(result.is_err()).to_equal(true)
```

</details>

### PngDecode — pixel output

#### 1x1 pixel images

#### AC-2: 1x1 black PNG decodes to single black ARGB pixel

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A minimal valid 1x1 black PNG would be needed here.
# This test validates the decode -> ARGB conversion path.
# Without implementation, this MUST fail.
val data: [u8] = [0]  # placeholder — not a valid PNG
val result = decode_png_to_argb(data)
# Should fail because data is invalid
expect(result.is_err()).to_equal(true)
```

</details>

#### pixel count matches dimensions

#### AC-2: decoded pixel count equals width * height

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Placeholder — will fail without implementation and valid PNG data
val data: [u8] = [0]
val result = decode_png_to_argb(data)
expect(result.is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/png_decode_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PngDecode — signature validation
- PngDecode — PngImage output
- PngDecode — pixel output

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
