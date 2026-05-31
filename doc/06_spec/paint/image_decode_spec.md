# Image Decode Specification

## Scenarios

### Image decode

### format detection

#### builds a complete in-memory BMP fixture

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _bmp_2x2_32()
expect(data.len()).to_equal(70)
expect(data[10:11].char_code_at(0)).to_equal(54)
expect(data[18:19].char_code_at(0)).to_equal(2)
expect(data[28:29].char_code_at(0)).to_equal(32)
```

</details>

#### detects BMP signature

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format(_bmp_2x2_32())).to_equal(ImageFormat.Bmp)
```

</details>

#### detects GIF signature

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format(_gif_10x10())).to_equal(ImageFormat.Gif)
```

</details>

#### detects JPEG signature

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format(_jpeg_3x2())).to_equal(ImageFormat.Jpeg)
```

</details>

#### detects PNG signature

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format(_png_2x1_indexed_red_green_alpha())).to_equal(ImageFormat.Png)
```

</details>

#### detects WebP RIFF signature

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format(_webp_vp8x_65x66())).to_equal(ImageFormat.Webp)
```

</details>

#### detects ICO signature

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format(_ico_64x33())).to_equal(ImageFormat.Ico)
```

</details>

#### detects SVG root text

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format(_svg_default())).to_equal(ImageFormat.Svg)
```

</details>

#### detects TIFF little-endian signature

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format(_tiff_le_3x2())).to_equal(ImageFormat.Tiff)
```

</details>

#### detects JPEG XL codestream signature

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format(_jpegxl_codestream())).to_equal(ImageFormat.JpegXl)
```

</details>

#### detects JPEG XL container signature

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format(_jpegxl_container())).to_equal(ImageFormat.JpegXl)
```

</details>

### BMP

#### decodes uncompressed 32-bit BMP pixels to RGBA in display order

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = decode_bmp(_bmp_2x2_32())

expect(image.width).to_equal(2)
expect(image.height).to_equal(2)
expect(image.format).to_equal(ImageFormat.Bmp)
expect(image.data).to_equal([
    80, 70, 60, 90,
    120, 110, 100, 122,
    60, 50, 40, 70,
    100, 90, 80, 110
])
```

</details>

### PNG

#### decodes indexed PLTE pixels with tRNS alpha to RGBA

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = decode_png(_png_2x1_indexed_red_green_alpha())

expect(image.width).to_equal(2)
expect(image.height).to_equal(1)
expect(image.format).to_equal(ImageFormat.Png)
expect(image.data).to_equal([
    255, 0, 0, 255,
    0, 255, 0, 128
])
```

</details>

#### decodes truecolor RGBA pixels without palette conversion

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = decode_png(_png_1x1_rgba())

expect(image.width).to_equal(1)
expect(image.height).to_equal(1)
expect(image.format).to_equal(ImageFormat.Png)
expect(image.data).to_equal([10, 20, 30, 40])
```

</details>

#### reconstructs sub-filtered truecolor RGB pixels

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = decode_png(_png_2x1_rgb_sub_filtered())

expect(image.width).to_equal(2)
expect(image.height).to_equal(1)
expect(image.format).to_equal(ImageFormat.Png)
expect(image.data).to_equal([
    10, 20, 30, 255,
    40, 50, 60, 255
])
```

</details>

### GIF

#### decodes first-frame palette pixels to RGBA

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = decode_gif(_gif_2x1_red_green())

expect(image.width).to_equal(2)
expect(image.height).to_equal(1)
expect(image.format).to_equal(ImageFormat.Gif)
expect(image.data).to_equal([
    255, 0, 0, 255,
    0, 255, 0, 255
])
```

</details>

#### falls back to intrinsic dimensions for GIF metadata without an image frame

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = decode_gif(_gif_10x10())

expect(image.width).to_equal(10)
expect(image.height).to_equal(10)
expect(image.format).to_equal(ImageFormat.Gif)
```

</details>

### JPEG

#### preserves intrinsic SOF dimensions for layout placeholder rendering

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = decode_jpeg(_jpeg_3x2())

expect(image.width).to_equal(3)
expect(image.height).to_equal(2)
expect(image.format).to_equal(ImageFormat.Jpeg)
expect(image.data.len()).to_equal(24)
expect(image.data[0]).to_equal(128)
expect(image.data[3]).to_equal(255)
```

</details>

### WebP

#### preserves VP8X intrinsic dimensions for layout placeholder rendering

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = decode_webp(_webp_vp8x_65x66())

expect(image.width).to_equal(65)
expect(image.height).to_equal(66)
expect(image.format).to_equal(ImageFormat.Webp)
expect(image.data.len()).to_be_greater_than(0)
```

</details>

### ICO

#### decodes BMP-backed 32-bit ICO pixels to RGBA in display order

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = decode_ico(_ico_2x2_bmp32())

expect(image.width).to_equal(2)
expect(image.height).to_equal(2)
expect(image.format).to_equal(ImageFormat.Ico)
expect(image.data).to_equal([
    80, 70, 60, 90,
    120, 110, 100, 122,
    60, 50, 40, 70,
    100, 90, 80, 110
])
```

</details>

#### preserves directory intrinsic dimensions for layout placeholder rendering

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = decode_ico(_ico_64x33())

expect(image.width).to_equal(64)
expect(image.height).to_equal(33)
expect(image.format).to_equal(ImageFormat.Ico)
expect(image.data.len()).to_be_greater_than(0)
```

</details>

### TIFF

#### parses little-endian baseline metadata and returns a fail-closed placeholder

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = detect_image_info(_tiff_le_3x2())
expect(info.format).to_equal("tiff")
expect(info.width).to_equal(3)
expect(info.height).to_equal(2)
expect(info.supported).to_equal(true)

val image = decode_tiff(_tiff_le_3x2())
expect(image.width).to_equal(3)
expect(image.height).to_equal(2)
expect(image.format).to_equal(ImageFormat.Tiff)
expect(image.data.len()).to_equal(24)
```

</details>

#### parses big-endian baseline metadata

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = detect_image_info(_tiff_be_4x5())
expect(info.format).to_equal("tiff")
expect(info.width).to_equal(4)
expect(info.height).to_equal(5)
expect(info.supported).to_equal(true)
```

</details>

#### decodes little-endian uncompressed RGB strips to RGBA pixels

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = decode_tiff(_tiff_le_2x1_rgb())

expect(image.width).to_equal(2)
expect(image.height).to_equal(1)
expect(image.format).to_equal(ImageFormat.Tiff)
expect(image.data).to_equal([
    10, 20, 30, 255,
    40, 50, 60, 255
])
```

</details>

#### decodes little-endian uncompressed RGBA strips with alpha

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = decode_tiff(_tiff_le_1x1_rgba())

expect(image.width).to_equal(1)
expect(image.height).to_equal(1)
expect(image.format).to_equal(ImageFormat.Tiff)
expect(image.data).to_equal([70, 80, 90, 100])
```

</details>

### JPEG XL

#### detects JPEG XL signatures but keeps decode fail-closed

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = detect_image_info(_jpegxl_container())
expect(info.format).to_equal("jpegxl")
expect(info.supported).to_equal(false)
expect(info.reason).to_equal("jpegxl-signature-detected-decoder-pending")

val image = decode_jpegxl(_jpegxl_container())
expect(image.width).to_equal(1)
expect(image.height).to_equal(1)
expect(image.format).to_equal(ImageFormat.JpegXl)
```

</details>

### SVG

#### uses the browser default intrinsic SVG object size

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = decode_svg(_svg_default())

expect(image.width).to_equal(300)
expect(image.height).to_equal(150)
expect(image.format).to_equal(ImageFormat.Svg)
```

</details>

#### preserves explicit SVG root width and height

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = decode_svg(_svg_explicit_size())

expect(image.width).to_equal(10)
expect(image.height).to_equal(20)
expect(image.format).to_equal(ImageFormat.Svg)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `examples/browser/test/paint/image_decode_spec.spl` |
| Updated | 2026-05-31 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Image decode
- format detection
- BMP
- PNG
- GIF
- JPEG
- WebP
- ICO
- TIFF
- JPEG XL
- SVG

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

