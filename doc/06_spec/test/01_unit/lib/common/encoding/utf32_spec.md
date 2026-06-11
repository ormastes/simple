# Utf32 Specification

> <details>

<!-- sdn-diagram:id=utf32_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=utf32_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

utf32_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=utf32_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Utf32 Specification

## Scenarios

### utf32_encode_one

#### passes through valid codepoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(utf32_encode_one(0x41)).to_equal(0x41)
expect(utf32_encode_one(0xAC00)).to_equal(0xAC00)
expect(utf32_encode_one(0x1F600)).to_equal(0x1F600)
expect(utf32_encode_one(0x10FFFF)).to_equal(0x10FFFF)
expect(utf32_encode_one(0x00)).to_equal(0x00)
```

</details>

#### replaces surrogates with U+FFFD

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(utf32_encode_one(0xD800)).to_equal(0xFFFD)
expect(utf32_encode_one(0xDBFF)).to_equal(0xFFFD)
expect(utf32_encode_one(0xDC00)).to_equal(0xFFFD)
expect(utf32_encode_one(0xDFFF)).to_equal(0xFFFD)
```

</details>

#### replaces out-of-range with U+FFFD

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(utf32_encode_one(0x110000)).to_equal(0xFFFD)
expect(utf32_encode_one(-1)).to_equal(0xFFFD)
```

</details>

### utf32_decode_one

#### passes through valid values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(utf32_decode_one(0x41)).to_equal(0x41)
expect(utf32_decode_one(0xAC00)).to_equal(0xAC00)
expect(utf32_decode_one(0x1F600)).to_equal(0x1F600)
```

</details>

#### replaces surrogates with U+FFFD

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(utf32_decode_one(0xD800)).to_equal(0xFFFD)
```

</details>

#### replaces out-of-range with U+FFFD

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(utf32_decode_one(0x110000)).to_equal(0xFFFD)
```

</details>

### utf32_encode_all and utf32_decode_all

#### roundtrips valid codepoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cps = [0x41, 0xAC00, 0x1F600, 0x4F60]
val encoded = utf32_encode_all(cps)
expect(encoded.len()).to_equal(4)
val decoded = utf32_decode_all(encoded)
expect(decoded).to_equal(cps)
```

</details>

#### roundtrips Korean

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cps = [0xAC00, 0xB098, 0xB2E4]
val encoded = utf32_encode_all(cps)
val decoded = utf32_decode_all(encoded)
expect(decoded).to_equal(cps)
```

</details>

#### roundtrips Cyrillic

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cps = [0x041F, 0x0440, 0x0438, 0x0432, 0x0435, 0x0442]
val encoded = utf32_encode_all(cps)
val decoded = utf32_decode_all(encoded)
expect(decoded).to_equal(cps)
```

</details>

#### handles empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = utf32_encode_all([])
expect(encoded.len()).to_equal(0)
val decoded = utf32_decode_all([])
expect(decoded.len()).to_equal(0)
```

</details>

#### replaces invalid codepoints in bulk

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mixed = [0x41, 0xD800, 0x42]
val encoded = utf32_encode_all(mixed)
expect(encoded[0]).to_equal(0x41)
expect(encoded[1]).to_equal(0xFFFD)
expect(encoded[2]).to_equal(0x42)
```

</details>

### utf32_to_bytes_le

#### serializes as little-endian 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# U+0041 -> 41 00 00 00
val bytes = utf32_to_bytes_le([0x41])
expect(bytes.len()).to_equal(4)
expect(bytes[0]).to_equal(0x41)
expect(bytes[1]).to_equal(0x00)
expect(bytes[2]).to_equal(0x00)
expect(bytes[3]).to_equal(0x00)
```

</details>

#### serializes Hangul as little-endian

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# U+AC00 -> 00 AC 00 00
val bytes = utf32_to_bytes_le([0xAC00])
expect(bytes.len()).to_equal(4)
expect(bytes[0]).to_equal(0x00)
expect(bytes[1]).to_equal(0xAC)
expect(bytes[2]).to_equal(0x00)
expect(bytes[3]).to_equal(0x00)
```

</details>

### utf32_to_bytes_be

#### serializes as big-endian 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# U+0041 -> 00 00 00 41
val bytes = utf32_to_bytes_be([0x41])
expect(bytes.len()).to_equal(4)
expect(bytes[0]).to_equal(0x00)
expect(bytes[1]).to_equal(0x00)
expect(bytes[2]).to_equal(0x00)
expect(bytes[3]).to_equal(0x41)
```

</details>

### utf32 bytes roundtrip

#### roundtrips LE serialization

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [0x41, 0xAC00, 0x1F600]
val bytes = utf32_to_bytes_le(values)
val restored = utf32_from_bytes_le(bytes)
expect(restored).to_equal(values)
```

</details>

#### roundtrips BE serialization

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [0x41, 0xAC00, 0x1F600]
val bytes = utf32_to_bytes_be(values)
val restored = utf32_from_bytes_be(bytes)
expect(restored).to_equal(values)
```

</details>

### utf32 to utf8 cross-codec

#### converts ASCII

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val utf32_values = [0x48, 0x69]
val utf8_bytes = utf32_to_utf8(utf32_values)
expect(utf8_bytes).to_equal([0x48, 0x69])
```

</details>

#### converts Korean

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val utf32_values = [0xAC00]
val utf8_bytes = utf32_to_utf8(utf32_values)
expect(utf8_bytes.len()).to_equal(3)
expect(utf8_bytes[0]).to_equal(0xEA)
expect(utf8_bytes[1]).to_equal(0xB0)
expect(utf8_bytes[2]).to_equal(0x80)
```

</details>

#### converts emoji

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val utf32_values = [0x1F600]
val utf8_bytes = utf32_to_utf8(utf32_values)
expect(utf8_bytes.len()).to_equal(4)
expect(utf8_bytes[0]).to_equal(0xF0)
expect(utf8_bytes[1]).to_equal(0x9F)
expect(utf8_bytes[2]).to_equal(0x98)
expect(utf8_bytes[3]).to_equal(0x80)
```

</details>

### utf8 to utf32 cross-codec

#### converts ASCII

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val utf8_bytes = [0x48, 0x69]
val utf32_values = utf8_to_utf32(utf8_bytes)
expect(utf32_values).to_equal([0x48, 0x69])
```

</details>

#### converts Korean

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val utf8_bytes = [0xEA, 0xB0, 0x80]
val utf32_values = utf8_to_utf32(utf8_bytes)
expect(utf32_values.len()).to_equal(1)
expect(utf32_values[0]).to_equal(0xAC00)
```

</details>

#### roundtrips 12-language codepoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# One representative codepoint from each script
val cps = [
    0x41,     # Latin A
    0xE9,     # Latin e-acute
    0xDF,     # German eszett
    0x041F,   # Cyrillic Pe
    0x0391,   # Greek Alpha
    0x0645,   # Arabic Meem
    0x05D0,   # Hebrew Alef
    0x0928,   # Devanagari Na
    0x0E01,   # Thai Ko Kai
    0x01B0,   # Vietnamese u-horn
    0x4F60,   # Chinese ni
    0x3053,   # Japanese Hiragana ko
    0xAC00    # Korean ga
]
val utf8_bytes = utf32_to_utf8(cps)
val restored = utf8_to_utf32(utf8_bytes)
expect(restored).to_equal(cps)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/utf32_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- utf32_encode_one
- utf32_decode_one
- utf32_encode_all and utf32_decode_all
- utf32_to_bytes_le
- utf32_to_bytes_be
- utf32 bytes roundtrip
- utf32 to utf8 cross-codec
- utf8 to utf32 cross-codec

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
