# Colrv1 Specification

> <details>

<!-- sdn-diagram:id=colrv1_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=colrv1_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

colrv1_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=colrv1_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Colrv1 Specification

## Scenarios

### parse_colr_header

#### returns None when blob is too short

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf: [u8] = [0, 1, 0, 2]
val result = parse_colr_header(buf)
expect(result == None).to_equal(true)
```

</details>

#### returns Some with correct fields for a valid version-1 header

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Byte layout (20 bytes):
#  0-1  version = 0x0001
#  2-3  numBaseGlyphRecords = 0x0002
#  4-7  baseGlyphRecordsOffset = 0x0000000E (14)
#  8-11 layerListOffset = 0x0000001C (28)
# 12-15 clipListOffset = 0x00000000
# 16-19 varIndexMapOffset = 0x00000000
val buf: [u8] = [
    0, 1,
    0, 2,
    0, 0, 0, 14,
    0, 0, 0, 28,
    0, 0, 0, 0,
    0, 0, 0, 0
]
val result = parse_colr_header(buf)
expect(result == None).to_equal(false)
val hdr = result.unwrap()
expect(hdr.version as i64).to_equal(1)
expect(hdr.num_base_glyph_records as i64).to_equal(2)
expect(hdr.layer_list_offset as i64).to_equal(28)
expect(hdr.clip_list_offset as i64).to_equal(0)
expect(hdr.var_index_map_offset as i64).to_equal(0)
```

</details>

#### returns None for a version-0 COLR table (not v1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# version byte = 0x0000
val buf: [u8] = [
    0, 0,
    0, 2,
    0, 0, 0, 14,
    0, 0, 0, 28,
    0, 0, 0, 0,
    0, 0, 0, 0
]
val result = parse_colr_header(buf)
expect(result == None).to_equal(true)
```

</details>

### parse_layer_list

#### returns empty list when layer_list_offset is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf: [u8] = [
    0, 1,
    0, 0,
    0, 0, 0, 14,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0
]
val maybe_hdr = parse_colr_header(buf)
val hdr = maybe_hdr.unwrap()
val layers = parse_layer_list(buf, hdr)
expect(layers.len()).to_equal(0)
```

</details>

#### returns layers when layer_list_offset points to valid data

<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build a buffer that has:
#   COLR v1 header (20 bytes, offsets as above)
#   8 bytes padding to reach offset 28
#   layer list: numLayers=2 (4 bytes) + 2 records x 6 bytes = 16 bytes
# Total = 20 + 8 + 4 + 12 = 44 bytes
# header: version=1, numBase=0, baseGlyphOff=14, layerListOff=28, clip=0, var=0
# Pad bytes 20-27 = 8 zero bytes
# At offset 28: numLayers = 0x00000002
# Record 0: glyphId=0x0001, paintOffset=0x00000020
# Record 1: glyphId=0x0002, paintOffset=0x00000026
val buf: [u8] = [
    0, 1,
    0, 0,
    0, 0, 0, 14,
    0, 0, 0, 28,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 2,
    0, 1, 0, 0, 0, 32,
    0, 2, 0, 0, 0, 38
]
val maybe_hdr = parse_colr_header(buf)
val hdr = maybe_hdr.unwrap()
val layers = parse_layer_list(buf, hdr)
expect(layers.len()).to_equal(2)
val l0 = layers[0]
expect(l0.glyph_id as i64).to_equal(1)
expect(l0.paint_offset as i64).to_equal(32)
val l1 = layers[1]
expect(l1.glyph_id as i64).to_equal(2)
expect(l1.paint_offset as i64).to_equal(38)
```

</details>

### decode_paint_subtable

#### returns Some(PaintNode) with kind Solid for format byte 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# format=2, palette_index=0x0003
val buf: [u8] = [2, 0, 3, 0, 0, 0]
val result = decode_paint_subtable(buf, 0)
expect(result == None).to_equal(false)
val node = result.unwrap()
expect(node.alpha_fixed).to_equal(16384)
```

</details>

#### returns Some with Solid fallback for unknown format byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# format=99 — unknown
val buf: [u8] = [99, 0, 0]
val result = decode_paint_subtable(buf, 0)
expect(result == None).to_equal(false)
val node = result.unwrap()
expect(node.alpha_fixed).to_equal(16384)
```

</details>

#### returns None when offset is out of bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf: [u8] = [2, 0, 3]
val result = decode_paint_subtable(buf, 100)
expect(result == None).to_equal(true)
```

</details>

### route_color_glyph

#### returns None when colr_blob is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf: [u8] = []
val result = route_color_glyph(1, buf)
expect(result == None).to_equal(true)
```

</details>

#### returns None when COLR table has wrong version

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# version=0, too short for v1
val buf: [u8] = [
    0, 0,
    0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0
]
val result = route_color_glyph(1, buf)
expect(result == None).to_equal(true)
```

</details>

### PaintGraphContext

#### constructor preserves all 3 fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bounds = SkRect(left: 0.0, top: 0.0, right: 8.0, bottom: 8.0)
val palette: [SkColor] = [sk_color_argb(255, 200, 100, 50)]
val ctx = PaintGraphContext(bounds: bounds, palette: palette, em_units: 1000)
expect(ctx.em_units as i64).to_equal(1000)
expect(ctx.palette.len()).to_equal(1)
expect((ctx.bounds.right - ctx.bounds.left) as i64).to_equal(8)
```

</details>

### compose_paint_graph

#### Solid node fills bitmap center pixel with palette color alpha-scaled

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# blob: format=2 (Solid), palette_index=0 (bytes 1-2), then padding
# alpha_fixed is hardcoded to 0x4000 (16384) = 1.0 scale in decode_paint_subtable
val buf: [u8] = [2, 0, 0, 0, 0, 0]
val bounds = SkRect(left: 0.0, top: 0.0, right: 4.0, bottom: 4.0)
# Red fully-opaque color at palette index 0
val palette: [SkColor] = [sk_color_argb(255, 255, 0, 0)]
val ctx = PaintGraphContext(bounds: bounds, palette: palette, em_units: 1000)
val bmp = compose_paint_graph(buf, 0, ctx)
# Bitmap should be 4x4 and center pixel (2,2) should be red with full alpha
expect(bmp.width).to_equal(4)
expect(bmp.height).to_equal(4)
val cx = 2 as i64
val cy = 2 as i64
val idx = (cy * bmp.width + cx) * 4
# R channel should be non-zero (red)
expect(bmp.pixels[idx] as i64).to_be_greater_than(0)
# A channel should be non-zero (fully opaque)
expect(bmp.pixels[idx + 3] as i64).to_be_greater_than(0)
```

</details>

#### ColrLayers with two Solid layers — later layer color dominates under SrcOver

1. 11, 2, 0, 0, 0, 2,   # ColrLayers header
2. 2, 0, 0, 0, 0, 0,     # child1 Solid
3. 2, 0, 1, 0, 0, 0      # child2 Solid


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build a minimal blob that has:
#   offset 0: format=11 (ColrLayers), num_layers=2, first_layer_idx=0
#   The layer index table at word-offset 0 means entries at byte 0,4
#   We'll place both child Solid records inline after the header.
#
# Layout:
#   [0]  format=11, num_layers=2, first_layer_idx (4 bytes) = 2  (word index 2 → byte 8)
#   [6]  padding to reach byte 8
#   [8]  word[2] = byte offset of first child solid = 14  (u32 BE: 0,0,0,14)
#   [12] word[3] = byte offset of second child solid = 20 (u32 BE: 0,0,0,20)
#   [14] solid1: format=2, palette_index=0 (green, palette[0])
#   [20] solid2: format=2, palette_index=1 (blue, palette[1])
val buf: [u8] = [
    11, 2, 0, 0, 0, 2,   # ColrLayers header (6 bytes at offset 0)
    0, 0,                  # 2 bytes padding to reach offset 8
    0, 0, 0, 14,           # word[2]: child1 paint offset = 14
    0, 0, 0, 20,           # word[3]: child2 paint offset = 20
    2, 0, 0, 0, 0, 0,     # child1 Solid (palette_index=0) at offset 14
    2, 0, 1, 0, 0, 0      # child2 Solid (palette_index=1) at offset 20
]
val bounds = SkRect(left: 0.0, top: 0.0, right: 2.0, bottom: 2.0)
# palette[0] = green, palette[1] = blue (fully opaque)
val green: SkColor = sk_color_argb(255, 0, 200, 0)
val blue: SkColor  = sk_color_argb(255, 0, 0, 200)
val palette: [SkColor] = [green, blue]
val ctx = PaintGraphContext(bounds: bounds, palette: palette, em_units: 1000)
val bmp = compose_paint_graph(buf, 0, ctx)
# After SrcOver blending of blue over green, blue (index 1) should dominate.
# Check pixel (0,0): blue channel should exceed green channel.
val idx = 0 as i64
val r_ch = bmp.pixels[idx] as i64
val g_ch = bmp.pixels[idx + 1] as i64
val b_ch = bmp.pixels[idx + 2] as i64
val a_ch = bmp.pixels[idx + 3] as i64
expect(a_ch).to_be_greater_than(0)
expect(b_ch).to_be_greater_than(g_ch)
```

</details>

#### out-of-bounds paint_offset returns zeros bitmap without crashing

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf: [u8] = [2, 0, 0, 0, 0, 0]
val bounds = SkRect(left: 0.0, top: 0.0, right: 4.0, bottom: 4.0)
val palette: [SkColor] = []
val ctx = PaintGraphContext(bounds: bounds, palette: palette, em_units: 1000)
# Use an offset far beyond the blob
val bmp = compose_paint_graph(buf, 9999, ctx)
expect(bmp.width).to_equal(4)
expect(bmp.height).to_equal(4)
# All pixels should be zero (transparent)
val idx = 0 as i64
expect(bmp.pixels[idx] as i64).to_equal(0)
expect(bmp.pixels[idx + 3] as i64).to_equal(0)
```

</details>

#### PaintGlyph masks child paint output

<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Blob layout:
#   offset 0 (6 bytes): format=10 (PaintGlyph)
#     [0]=10 (format)
#     [1..3]=src_paint_offset (u24 BE) = 6
#     [4..5]=glyph_id (u16 BE) = 0 (unused — no font in context)
#   offset 6 (6 bytes): format=2 (Solid), palette_index=0
val buf: [u8] = [
    10, 0, 0, 6, 0, 0,   # PaintGlyph header -> child at offset 6
    2, 0, 0, 0, 0, 0      # Solid child, palette[0]
]
# 8x8 bitmap: large enough for corners to fall outside the circular
# mask and the center to be fully covered.
val bounds = SkRect(left: 0.0, top: 0.0, right: 8.0, bottom: 8.0)
val red: SkColor = sk_color_argb(255, 255, 0, 0)
val palette: [SkColor] = [red]
val ctx = PaintGraphContext(bounds: bounds, palette: palette, em_units: 1000)
val bmp = compose_paint_graph(buf, 0, ctx)
expect(bmp.width).to_equal(8)
expect(bmp.height).to_equal(8)
# Scan all pixels; count opaque (alpha>0) and transparent (alpha==0).
val total = bmp.width * bmp.height
var opaque_count = 0 as i64
var transparent_count = 0 as i64
var alpha_sum = 0 as i64
var i = 0 as i64
while i < total:
    val a_idx = i * 4 + 3
    val a = bmp.pixels[a_idx] as i64
    alpha_sum = alpha_sum + a
    if a > 0:
        opaque_count = opaque_count + 1
    else:
        transparent_count = transparent_count + 1
    i = i + 1
# Some pixels must be opaque (center under mask) ...
expect(alpha_sum).to_be_greater_than(0)
expect(opaque_count).to_be_greater_than(0)
# ... and some must be transparent (corners outside the circular mask).
expect(transparent_count).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/skia/colrv1_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- parse_colr_header
- parse_layer_list
- decode_paint_subtable
- route_color_glyph
- PaintGraphContext
- compose_paint_graph

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
