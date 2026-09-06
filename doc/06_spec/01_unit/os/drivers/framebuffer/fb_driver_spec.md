# Framebuffer Driver Specification

> Tests Color struct construction, ARGB packing, static color constructors, and the 8x16 bitmap font glyph lookup.

<!-- sdn-diagram:id=fb_driver_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fb_driver_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fb_driver_spec -> std
fb_driver_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fb_driver_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Framebuffer Driver Specification

Tests Color struct construction, ARGB packing, static color constructors, and the 8x16 bitmap font glyph lookup.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-FB |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/01_unit/os/drivers/framebuffer/fb_driver_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests Color struct construction, ARGB packing, static color constructors,
and the 8x16 bitmap font glyph lookup.

## Scenarios

### Color

### rgb

#### creates color with full alpha

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color.rgb(128, 64, 32)
expect(c.r).to_equal(128)
expect(c.g).to_equal(64)
expect(c.b).to_equal(32)
expect(c.a).to_equal(255)
```

</details>

#### creates color with zero components

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color.rgb(0, 0, 0)
expect(c.r).to_equal(0)
expect(c.g).to_equal(0)
expect(c.b).to_equal(0)
```

</details>

#### creates color with max components

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color.rgb(255, 255, 255)
expect(c.r).to_equal(255)
expect(c.g).to_equal(255)
expect(c.b).to_equal(255)
```

</details>

### to_u32

#### packs black as 0xFF000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color.black()
expect(c.to_u32()).to_equal(0xFF000000)
```

</details>

#### packs white as 0xFFFFFFFF

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color.white()
expect(c.to_u32()).to_equal(0xFFFFFFFF)
```

</details>

#### packs red as 0xFFFF0000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color.red()
expect(c.to_u32()).to_equal(0xFFFF0000)
```

</details>

#### packs green as 0xFF00FF00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color.green()
expect(c.to_u32()).to_equal(0xFF00FF00)
```

</details>

#### packs blue as 0xFF0000FF

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color.blue()
expect(c.to_u32()).to_equal(0xFF0000FF)
```

</details>

#### encodes alpha in bits 31-24

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color(r: 0, g: 0, b: 0, a: 128)
val alpha_bits = (c.to_u32() >> 24) & 0xFF
expect(alpha_bits).to_equal(128)
```

</details>

#### encodes red in bits 23-16

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color.rgb(0xAB, 0, 0)
val red_bits = (c.to_u32() >> 16) & 0xFF
expect(red_bits).to_equal(0xAB)
```

</details>

#### encodes green in bits 15-8

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color.rgb(0, 0xCD, 0)
val green_bits = (c.to_u32() >> 8) & 0xFF
expect(green_bits).to_equal(0xCD)
```

</details>

#### encodes blue in bits 7-0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color.rgb(0, 0, 0xEF)
val blue_bits = c.to_u32() & 0xFF
expect(blue_bits).to_equal(0xEF)
```

</details>

### static constructors

#### black is (0,0,0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color.black()
expect(c.r).to_equal(0)
expect(c.g).to_equal(0)
expect(c.b).to_equal(0)
```

</details>

#### white is (255,255,255)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color.white()
expect(c.r).to_equal(255)
expect(c.g).to_equal(255)
expect(c.b).to_equal(255)
```

</details>

#### red is (255,0,0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color.red()
expect(c.r).to_equal(255)
expect(c.g).to_equal(0)
expect(c.b).to_equal(0)
```

</details>

#### green is (0,255,0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color.green()
expect(c.r).to_equal(0)
expect(c.g).to_equal(255)
expect(c.b).to_equal(0)
```

</details>

#### blue is (0,0,255)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color.blue()
expect(c.r).to_equal(0)
expect(c.g).to_equal(0)
expect(c.b).to_equal(255)
```

</details>

#### gray is (128,128,128)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color.gray()
expect(c.r).to_equal(128)
expect(c.g).to_equal(128)
expect(c.b).to_equal(128)
```

</details>

#### dark_gray is (64,64,64)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color.dark_gray()
expect(c.r).to_equal(64)
expect(c.g).to_equal(64)
expect(c.b).to_equal(64)
```

</details>

#### light_gray is (192,192,192)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color.light_gray()
expect(c.r).to_equal(192)
expect(c.g).to_equal(192)
expect(c.b).to_equal(192)
```

</details>

### get_glyph_8x16

#### returns 16 bytes per glyph

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val glyph = get_glyph_8x16(0x41)  # 'A'
expect(glyph.len()).to_equal(16)
```

</details>

#### returns all zeros for space (0x20)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val glyph = get_glyph_8x16(0x20)
var all_zero = true
for byte in glyph:
    if byte != 0:
        all_zero = false
expect(all_zero).to_equal(true)
```

</details>

#### returns non-zero bitmap for A (0x41)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val glyph = get_glyph_8x16(0x41)
var has_nonzero = false
for byte in glyph:
    if byte != 0:
        has_nonzero = true
expect(has_nonzero).to_equal(true)
```

</details>

#### returns non-zero bitmap for B (0x42)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val glyph = get_glyph_8x16(0x42)
var has_nonzero = false
for byte in glyph:
    if byte != 0:
        has_nonzero = true
expect(has_nonzero).to_equal(true)
```

</details>

#### returns non-zero bitmap for S (0x53)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val glyph = get_glyph_8x16(0x53)
var has_nonzero = false
for byte in glyph:
    if byte != 0:
        has_nonzero = true
expect(has_nonzero).to_equal(true)
```

</details>

#### returns filled block for unknown char

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val glyph = get_glyph_8x16(0x7F)  # DEL - not defined, gets default
var all_ff = true
for byte in glyph:
    if byte != 0xFF:
        all_ff = false
expect(all_ff).to_equal(true)
```

</details>

#### space glyph first row is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val glyph = get_glyph_8x16(0x20)
expect(glyph[0]).to_equal(0x00)
```

</details>

#### A glyph has specific known row values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val glyph = get_glyph_8x16(0x41)
# Row 2 (index 2) = 0x10, Row 3 (index 3) = 0x38
expect(glyph[2]).to_equal(0x10)
expect(glyph[3]).to_equal(0x38)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
