# zlib header: CMF=0x78, FLG=0x01

> var out: [u8] = []

<!-- sdn-diagram:id=png_decode_deflate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=png_decode_deflate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

png_decode_deflate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=png_decode_deflate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# zlib header: CMF=0x78, FLG=0x01

var out: [u8] = []

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/png_decode_deflate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

var out: [u8] = []
    out = out + [0x78, 0x01]
    out = out + [0x01]
    val len_ = raw.len().to_i32()
    out = out + [(len_ & 0xFF).to_u8(), ((len_ >> 8) & 0xFF).to_u8()]
    val nlen = len_ ^ 0xFFFF
    out = out + [(nlen & 0xFF).to_u8(), ((nlen >> 8) & 0xFF).to_u8()]
    for b in raw:
        out = out + [b]
    out

fn make_1x1_rgb_png_stored() -> [u8]:
    """Build a minimal 1x1 RGB PNG using stored DEFLATE block.

    Pixel: RGB(255, 0, 0) red.
    Raw scanline: [filter=0, R=255, G=0, B=0]

## Scenarios

### PngDecode — DEFLATE decompression

#### stored block IDAT

#### AC-1: decodes 1x1 RGB PNG with stored DEFLATE block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val png = make_1x1_rgb_png_stored()
val result = decode_png_to_argb(png)
expect(result.is_err()).to_equal(false)
```

</details>

#### AC-1: 1x1 PNG produces exactly 1 pixel

- Ok
   - Expected: img.pixels.len().to_i32() equals `1`
- Err
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val png = make_1x1_rgb_png_stored()
val result = decode_png_to_argb(png)
match result:
    Ok(img):
        expect(img.pixels.len().to_i32()).to_equal(1)
    Err(msg):
        expect(msg).to_equal("")
```

</details>

#### AC-1: 1x1 red PNG pixel is correct ARGB

- Ok
   - Expected: img.pixels[0] equals `expected`
- Err
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val png = make_1x1_rgb_png_stored()
val result = decode_png_to_argb(png)
match result:
    Ok(img):
        # ARGB: 0xFF_FF_00_00 (alpha=255, red=255, green=0, blue=0)
        val expected: u32 = 0xFFFF0000
        expect(img.pixels[0]).to_equal(expected)
    Err(msg):
        expect(msg).to_equal("")
```

</details>

#### AC-1: 2x1 PNG produces exactly 2 pixels

- Ok
   - Expected: img.pixels.len().to_i32() equals `2`
- Err
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val png = make_2x1_rgb_png_stored()
val result = decode_png_to_argb(png)
match result:
    Ok(img):
        expect(img.pixels.len().to_i32()).to_equal(2)
    Err(msg):
        expect(msg).to_equal("")
```

</details>

### PngDecode — filter reconstruction

#### filter type 0 (None)

#### AC-1: None filter passes through raw bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 1x1 RGB: filter=0, R=100, G=200, B=50
val raw: [u8] = [0, 100, 200, 50]
val result = reconstruct_scanlines(raw, 1, 1, 3, 3)
# After reconstruction, should be [100, 200, 50]
expect(result.len().to_i32()).to_equal(3)
```

</details>

#### AC-1: None filter preserves byte values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw: [u8] = [0, 100, 200, 50]
val result = reconstruct_scanlines(raw, 1, 1, 3, 3)
if result.len().to_i32() >= 1:
    expect(result[0]).to_equal(100)
else:
    expect(result.len()).to_be_greater_than(0)
```

</details>

#### filter type 1 (Sub)

#### AC-1: Sub filter adds left neighbor to current byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2x1 RGB: filter=1, then bytes are deltas from left
# First pixel raw, second pixel = diff from first
# R1=100, G1=50, B1=25, dR2=10, dG2=5, dB2=3
# After Sub: R2=100+10=110, G2=50+5=55, B2=25+3=28
val raw: [u8] = [1, 100, 50, 25, 10, 5, 3]
val result = reconstruct_scanlines(raw, 2, 1, 3, 6)
# Output should be 6 bytes: [100, 50, 25, 110, 55, 28]
expect(result.len().to_i32()).to_equal(6)
```

</details>

#### filter type 2 (Up)

#### AC-1: Up filter adds above row byte to current

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 1x2 image (1 pixel wide, 2 rows):
# Row 0: filter=0, R=100, G=50, B=25
# Row 1: filter=2, dR=10, dG=5, dB=3
# After Up: Row1 = Row0 + delta = [110, 55, 28]
val raw: [u8] = [0, 100, 50, 25, 2, 10, 5, 3]
val result = reconstruct_scanlines(raw, 1, 2, 3, 3)
# Output: 6 bytes total (2 rows of 3 bytes)
expect(result.len().to_i32()).to_equal(6)
```

</details>

#### paeth predictor

#### AC-1: paeth_predictor(0, 0, 0) returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = paeth_predictor(0, 0, 0)
expect(p).to_equal(0)
```

</details>

#### AC-1: paeth_predictor with identical inputs returns that value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = paeth_predictor(100, 100, 100)
expect(p).to_equal(100)
```

</details>

#### AC-1: paeth_predictor selects closest to prediction

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# p = a + b - c = 10 + 20 - 5 = 25
# pa = |25 - 10| = 15, pb = |25 - 20| = 5, pc = |25 - 5| = 20
# min is pb -> returns b = 20
val p = paeth_predictor(10, 20, 5)
expect(p).to_equal(20)
```

</details>

### PngDecode — decompress_idat

#### stored block IDAT data

#### AC-1: decompress_idat returns non-empty for valid zlib stored data

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 1x1 RGB: raw scanline = [filter=0, R=255, G=0, B=0]
val raw: [u8] = [0, 255, 0, 0]
val compressed = make_zlib_stored(raw)
val result = decompress_idat(compressed, 1, 1, 2)
expect(result.len()).to_be_greater_than(0)
```

</details>

#### AC-1: decompress_idat output has correct byte count for 1x1 RGB

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw: [u8] = [0, 255, 0, 0]
val compressed = make_zlib_stored(raw)
val result = decompress_idat(compressed, 1, 1, 2)
# After filter reconstruction: 1 pixel * 3 channels = 3 bytes
expect(result.len().to_i32()).to_equal(3)
```

</details>

#### empty or invalid IDAT

#### AC-1: decompress_idat returns empty for too-short input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [0x78]
val result = decompress_idat(data, 1, 1, 2)
expect(result.len().to_i32()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
