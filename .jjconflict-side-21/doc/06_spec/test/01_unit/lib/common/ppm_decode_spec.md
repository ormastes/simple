# ppm_decode_spec

> Validates that the decoder correctly parses the PPM P6 magic number,

<!-- sdn-diagram:id=ppm_decode_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ppm_decode_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ppm_decode_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ppm_decode_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ppm_decode_spec

Validates that the decoder correctly parses the PPM P6 magic number,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ppm_decode_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## PPM P6 Header Parsing

    Validates that the decoder correctly parses the PPM P6 magic number,
    width/height dimensions, max value, and handles comments in the header.

## Scenarios

### PpmDecode — header parsing

#### valid PPM headers

#### AC-1: decodes valid 1x1 red PPM successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = make_ppm_1x1_red()
val result = decode_ppm_to_argb(data)
expect(result.is_err()).to_equal(false)
```

</details>

#### AC-1: parsed width is correct for 2x2 image

- Ok
   - Expected: img.width equals `2`
- Err
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = make_ppm_2x2_colors()
val result = decode_ppm_to_argb(data)
match result:
    Ok(img):
        expect(img.width).to_equal(2)
    Err(msg):
        expect(msg).to_equal("")
```

</details>

#### AC-1: parsed height is correct for 2x2 image

- Ok
   - Expected: img.height equals `2`
- Err
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = make_ppm_2x2_colors()
val result = decode_ppm_to_argb(data)
match result:
    Ok(img):
        expect(img.height).to_equal(2)
    Err(msg):
        expect(msg).to_equal("")
```

</details>

#### AC-1: handles comment lines in PPM header

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = make_ppm_with_comment()
val result = decode_ppm_to_argb(data)
expect(result.is_err()).to_equal(false)
```

</details>

#### invalid PPM headers

#### AC-1: rejects empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = []
val result = decode_ppm_to_argb(data)
expect(result.is_err()).to_equal(true)
```

</details>

#### AC-1: rejects non-PPM magic bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [0, 1, 2, 3, 4, 5]
val result = decode_ppm_to_argb(data)
expect(result.is_err()).to_equal(true)
```

</details>

#### AC-1: rejects P5 grayscale magic (only P6 supported)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "P5\n" = [80, 53, 10]
val data: [u8] = [80, 53, 10, 49, 32, 49, 10, 50, 53, 53, 10, 128]
val result = decode_ppm_to_argb(data)
expect(result.is_err()).to_equal(true)
```

</details>

#### AC-1: rejects truncated header (no dimensions)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [80, 54, 10]
val result = decode_ppm_to_argb(data)
expect(result.is_err()).to_equal(true)
```

</details>

### PpmDecode — pixel conversion

#### single pixel conversion

#### AC-1: red pixel converts to correct ARGB u32

- Ok
   - Expected: img.pixels[0] equals `expected`
- Err
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = make_ppm_1x1_red()
val result = decode_ppm_to_argb(data)
match result:
    Ok(img):
        # ARGB for red: 0xFF_FF_00_00
        val expected: u32 = 0xFFFF0000
        expect(img.pixels[0]).to_equal(expected)
    Err(msg):
        expect(msg).to_equal("")
```

</details>

#### AC-1: all pixels have alpha = 0xFF

- Ok
   - Expected: all_opaque is true
- Err
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = make_ppm_2x2_colors()
val result = decode_ppm_to_argb(data)
match result:
    Ok(img):
        var all_opaque = true
        for px in img.pixels:
            if (px >> 24) != 0xFF:
                all_opaque = false
        expect(all_opaque).to_equal(true)
    Err(msg):
        expect(msg).to_equal("")
```

</details>

#### multi-pixel images

#### AC-1: 2x2 image has exactly 4 pixels

- Ok
   - Expected: img.pixels.len().to_i32() equals `4`
- Err
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = make_ppm_2x2_colors()
val result = decode_ppm_to_argb(data)
match result:
    Ok(img):
        expect(img.pixels.len().to_i32()).to_equal(4)
    Err(msg):
        expect(msg).to_equal("")
```

</details>

#### AC-1: pixel count equals width * height

- Ok
   - Expected: img.pixels.len().to_i32() equals `expected`
- Err
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = make_ppm_3x1_black()
val result = decode_ppm_to_argb(data)
match result:
    Ok(img):
        val expected = img.width * img.height
        expect(img.pixels.len().to_i32()).to_equal(expected)
    Err(msg):
        expect(msg).to_equal("")
```

</details>

#### AC-1: green pixel at position 1 in 2x2 image

- Ok
   - Expected: img.pixels[1] equals `expected`
- Err
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = make_ppm_2x2_colors()
val result = decode_ppm_to_argb(data)
match result:
    Ok(img):
        # ARGB for green: 0xFF_00_FF_00
        val expected: u32 = 0xFF00FF00
        expect(img.pixels[1]).to_equal(expected)
    Err(msg):
        expect(msg).to_equal("")
```

</details>

#### AC-1: blue pixel at position 2 in 2x2 image

- Ok
   - Expected: img.pixels[2] equals `expected`
- Err
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = make_ppm_2x2_colors()
val result = decode_ppm_to_argb(data)
match result:
    Ok(img):
        # ARGB for blue: 0xFF_00_00_FF
        val expected: u32 = 0xFF0000FF
        expect(img.pixels[2]).to_equal(expected)
    Err(msg):
        expect(msg).to_equal("")
```

</details>

#### AC-1: black pixels decode to 0xFF000000

- Ok
   - Expected: img.pixels[0] equals `expected`
- Err
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = make_ppm_3x1_black()
val result = decode_ppm_to_argb(data)
match result:
    Ok(img):
        val expected: u32 = 0xFF000000
        expect(img.pixels[0]).to_equal(expected)
    Err(msg):
        expect(msg).to_equal("")
```

</details>

### PpmDecode — edge cases

#### truncated pixel data

#### AC-1: rejects PPM with missing pixel data

- data = data + [255, 0, 0]          # only 1 pixel
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Valid header for 2x2 but only 1 pixel of data (3 bytes instead of 12)
var data: [u8] = []
data = data + [80, 54, 10]         # P6\n
data = data + [50, 32, 50, 10]     # 2 2\n
data = data + [50, 53, 53, 10]     # 255\n
data = data + [255, 0, 0]          # only 1 pixel (need 4)
val result = decode_ppm_to_argb(data)
expect(result.is_err()).to_equal(true)
```

</details>

#### AC-1: encoder rejects dimensions that exceed supplied pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_ppm_p6(2u32, 2u32, [0xFF000000u32])
expect(encoded.len()).to_equal(0)
```

</details>

#### AC-1: rejects PPM dimensions too large to size safely

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = []
data = data + [80, 54, 10]                 # P6\n
data = data + [49, 48, 48, 48, 48, 48, 10] # 100000\n
data = data + [49, 48, 48, 48, 48, 48, 10] # 100000\n
data = data + [50, 53, 53, 10]             # 255\n
val result = decode_ppm_to_argb(data)
expect(result.is_err()).to_equal(true)
```

</details>

#### PpmImage struct fields

#### AC-1: PpmImage width field is accessible

- Ok
   - Expected: img.width equals `1`
- Err
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = make_ppm_1x1_red()
val result = decode_ppm_to_argb(data)
match result:
    Ok(img):
        expect(img.width).to_equal(1)
    Err(msg):
        expect(msg).to_equal("")
```

</details>

#### AC-1: PpmImage height field is accessible

- Ok
   - Expected: img.height equals `1`
- Err
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = make_ppm_1x1_red()
val result = decode_ppm_to_argb(data)
match result:
    Ok(img):
        expect(img.height).to_equal(1)
    Err(msg):
        expect(msg).to_equal("")
```

</details>

#### AC-1: PpmImage pixels field is accessible

- Ok
- Err
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = make_ppm_1x1_red()
val result = decode_ppm_to_argb(data)
match result:
    Ok(img):
        expect(img.pixels.len()).to_be_greater_than(0)
    Err(msg):
        expect(msg).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
