# Skia Raw-RGBA Codec Specification

> Tests for encode_raw_rgba / decode_raw_rgba — the trivial bitmap codec used to persist Bitmap instances for snapshot/golden tests. The format is a tiny 16-byte header (magic + version + width + height) followed by raw RGBA bytes. It is NOT a real image format and does not interoperate with PNG/JPEG.

<!-- sdn-diagram:id=raw_rgba_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=raw_rgba_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

raw_rgba_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=raw_rgba_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Raw-RGBA Codec Specification

Tests for encode_raw_rgba / decode_raw_rgba — the trivial bitmap codec used to persist Bitmap instances for snapshot/golden tests. The format is a tiny 16-byte header (magic + version + width + height) followed by raw RGBA bytes. It is NOT a real image format and does not interoperate with PNG/JPEG.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-CODEC-001 |
| Category | Stdlib |
| Difficulty | 1/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/raw_rgba_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for encode_raw_rgba / decode_raw_rgba — the trivial bitmap codec used
to persist Bitmap instances for snapshot/golden tests. The format is a tiny
16-byte header (magic + version + width + height) followed by raw RGBA
bytes. It is NOT a real image format and does not interoperate with PNG/JPEG.

## Scenarios

### raw_rgba codec

#### encode_raw_rgba: header is 16 bytes with correct magic

<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bmp = Bitmap.zeros(2, 3)
val blob = encode_raw_rgba(bmp)
# Magic bytes: 'R','B','P','A' = 0x52,0x42,0x50,0x41
val b0 = blob[0] as i64
val b1 = blob[1] as i64
val b2 = blob[2] as i64
val b3 = blob[3] as i64
expect(b0).to_equal(0x52)
expect(b1).to_equal(0x42)
expect(b2).to_equal(0x50)
expect(b3).to_equal(0x41)
# Version u32 = 1 (bytes 4..8 big-endian)
val v0 = blob[4] as i64
val v1 = blob[5] as i64
val v2 = blob[6] as i64
val v3 = blob[7] as i64
expect(v0).to_equal(0)
expect(v1).to_equal(0)
expect(v2).to_equal(0)
expect(v3).to_equal(1)
# Width (bytes 8..12) big-endian = 2
val w3 = blob[11] as i64
expect(w3).to_equal(2)
# Height (bytes 12..16) big-endian = 3
val h3 = blob[15] as i64
expect(h3).to_equal(3)
# Magic constant sanity
expect(RAW_RGBA_MAGIC).to_equal(1380012353)
```

</details>

#### decode_raw_rgba: empty blob returns None

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = [u8]()
val result = decode_raw_rgba(empty)
expect(result).to_be_nil()
```

</details>

#### decode_raw_rgba: wrong magic returns None

1. var bad = [u8]
2. bad push


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bad = [u8]()
var i = 0
while i < 32:
    bad.push(0 as u8)
    i = i + 1
val result = decode_raw_rgba(bad)
expect(result).to_be_nil()
```

</details>

#### decode_raw_rgba: truncated blob returns None

1. var truncated = [u8]
2. truncated push


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Valid header claims 4x4 (=64 bytes of pixels) but we only supply
# header + a few pixel bytes, so decode must reject.
val bmp = Bitmap.zeros(4, 4)
val full = encode_raw_rgba(bmp)
var truncated = [u8]()
var i = 0
while i < 20:
    truncated.push(full[i])
    i = i + 1
val result = decode_raw_rgba(truncated)
expect(result).to_be_nil()
```

</details>

#### encode then decode: round-trip preserves dimensions and pixels

1. var bmp = Bitmap zeros
2. bmp pixels[k] =
   - Expected: decoded.width equals `3`
   - Expected: decoded.height equals `2`
   - Expected: decoded.pixels.len() equals `3 * 2 * 4`
   - Expected: all_match is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bmp = Bitmap.zeros(3, 2)
# Stamp a recognizable pattern: each byte = its index.
var k = 0
while k < bmp.pixels.len():
    bmp.pixels[k] = (k as u8)
    k = k + 1
val blob = encode_raw_rgba(bmp)
val decoded_opt = decode_raw_rgba(blob)
if val decoded = decoded_opt:
    expect(decoded.width).to_equal(3)
    expect(decoded.height).to_equal(2)
    expect(decoded.pixels.len()).to_equal(3 * 2 * 4)
    var all_match = true
    var j = 0
    while j < decoded.pixels.len():
        val a = decoded.pixels[j] as i64
        val b = bmp.pixels[j] as i64
        if a != b:
            all_match = false
        j = j + 1
    expect(all_match).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### encode_raw_rgba: byte length is 16 + width*height*4

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bmp = Bitmap.zeros(5, 7)
val blob = encode_raw_rgba(bmp)
val expected_len = 16 + 5 * 7 * 4
expect(blob.len()).to_equal(expected_len)
expect(blob.len()).to_be_greater_than(16)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
