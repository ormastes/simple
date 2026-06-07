# Utf16 Specification

> <details>

<!-- sdn-diagram:id=utf16_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=utf16_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

utf16_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=utf16_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Utf16 Specification

## Scenarios

### utf16_encode_one

#### encodes BMP codepoint as single unit

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# U+0041 = 'A'
val result = utf16_encode_one(0x41)
expect(result.len()).to_equal(1)
expect(result[0]).to_equal(0x41)
```

</details>

#### encodes Hangul as single unit

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# U+AC00 가
val result = utf16_encode_one(0xAC00)
expect(result.len()).to_equal(1)
expect(result[0]).to_equal(0xAC00)
```

</details>

#### encodes supplementary as surrogate pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# U+1F600 -> D83D DE00
val result = utf16_encode_one(0x1F600)
expect(result.len()).to_equal(2)
expect(result[0]).to_equal(0xD83D)
expect(result[1]).to_equal(0xDE00)
```

</details>

#### encodes U+10000 as first surrogate pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# U+10000 -> D800 DC00
val result = utf16_encode_one(0x10000)
expect(result.len()).to_equal(2)
expect(result[0]).to_equal(0xD800)
expect(result[1]).to_equal(0xDC00)
```

</details>

#### encodes U+10FFFF as last valid surrogate pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# U+10FFFF -> DBFF DFFF
val result = utf16_encode_one(0x10FFFF)
expect(result.len()).to_equal(2)
expect(result[0]).to_equal(0xDBFF)
expect(result[1]).to_equal(0xDFFF)
```

</details>

#### replaces surrogates with U+FFFD

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = utf16_encode_one(0xD800)
expect(result[0]).to_equal(0xFFFD)
```

</details>

#### replaces out-of-range with U+FFFD

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = utf16_encode_one(0x110000)
expect(result[0]).to_equal(0xFFFD)
```

</details>

#### replaces negative with U+FFFD

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = utf16_encode_one(-1)
expect(result[0]).to_equal(0xFFFD)
```

</details>

### utf16_decode_one

#### decodes BMP code unit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = utf16_decode_one([0x41], 0)
expect(result[0]).to_equal(0x41)
expect(result[1]).to_equal(1)
```

</details>

#### decodes Hangul code unit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = utf16_decode_one([0xAC00], 0)
expect(result[0]).to_equal(0xAC00)
expect(result[1]).to_equal(1)
```

</details>

#### decodes surrogate pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# D83D DE00 -> U+1F600
val result = utf16_decode_one([0xD83D, 0xDE00], 0)
expect(result[0]).to_equal(0x1F600)
expect(result[1]).to_equal(2)
```

</details>

#### replaces lone high surrogate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = utf16_decode_one([0xD800], 0)
expect(result[0]).to_equal(0xFFFD)
```

</details>

#### replaces lone low surrogate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = utf16_decode_one([0xDC00], 0)
expect(result[0]).to_equal(0xFFFD)
```

</details>

#### decodes at nonzero offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = utf16_decode_one([0x41, 0x42, 0x43], 1)
expect(result[0]).to_equal(0x42)
expect(result[1]).to_equal(1)
```

</details>

### utf16_encode_all and utf16_decode_all

#### roundtrips ASCII

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cps = [0x48, 0x65, 0x6C, 0x6C, 0x6F]
val encoded = utf16_encode_all(cps)
expect(encoded.len()).to_equal(5)  # all BMP
val decoded = utf16_decode_all(encoded)
expect(decoded).to_equal(cps)
```

</details>

#### roundtrips Korean

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 가나다 = U+AC00 U+B098 U+B2E4
val cps = [0xAC00, 0xB098, 0xB2E4]
val encoded = utf16_encode_all(cps)
expect(encoded.len()).to_equal(3)  # all BMP
val decoded = utf16_decode_all(encoded)
expect(decoded).to_equal(cps)
```

</details>

#### roundtrips emoji with surrogates

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cps = [0x1F600, 0x1F601, 0x1F602]
val encoded = utf16_encode_all(cps)
expect(encoded.len()).to_equal(6)  # 2 units each
val decoded = utf16_decode_all(encoded)
expect(decoded).to_equal(cps)
```

</details>

#### roundtrips mixed BMP and supplementary

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 'A' + U+AC00 + U+1F600
val cps = [0x41, 0xAC00, 0x1F600]
val encoded = utf16_encode_all(cps)
expect(encoded.len()).to_equal(4)  # 1+1+2
val decoded = utf16_decode_all(encoded)
expect(decoded).to_equal(cps)
```

</details>

#### roundtrips CJK ideographs

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 你好世界 = U+4F60 U+597D U+4E16 U+754C
val cps = [0x4F60, 0x597D, 0x4E16, 0x754C]
val encoded = utf16_encode_all(cps)
expect(encoded.len()).to_equal(4)
val decoded = utf16_decode_all(encoded)
expect(decoded).to_equal(cps)
```

</details>

#### handles empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = utf16_encode_all([])
expect(encoded.len()).to_equal(0)
val decoded = utf16_decode_all([])
expect(decoded.len()).to_equal(0)
```

</details>

### utf16_to_bytes_le

#### serializes BMP as little-endian

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# U+0041 -> 41 00
val bytes = utf16_to_bytes_le([0x41])
expect(bytes.len()).to_equal(2)
expect(bytes[0]).to_equal(0x41)
expect(bytes[1]).to_equal(0x00)
```

</details>

#### serializes Hangul as little-endian

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# U+AC00 -> 00 AC
val bytes = utf16_to_bytes_le([0xAC00])
expect(bytes.len()).to_equal(2)
expect(bytes[0]).to_equal(0x00)
expect(bytes[1]).to_equal(0xAC)
```

</details>

### utf16_to_bytes_be

#### serializes BMP as big-endian

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# U+0041 -> 00 41
val bytes = utf16_to_bytes_be([0x41])
expect(bytes.len()).to_equal(2)
expect(bytes[0]).to_equal(0x00)
expect(bytes[1]).to_equal(0x41)
```

</details>

#### serializes Hangul as big-endian

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# U+AC00 -> AC 00
val bytes = utf16_to_bytes_be([0xAC00])
expect(bytes.len()).to_equal(2)
expect(bytes[0]).to_equal(0xAC)
expect(bytes[1]).to_equal(0x00)
```

</details>

### utf16 bytes roundtrip

#### roundtrips LE serialization

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val units = [0x41, 0xAC00, 0x4F60]
val bytes = utf16_to_bytes_le(units)
val restored = utf16_from_bytes_le(bytes)
expect(restored).to_equal(units)
```

</details>

#### roundtrips BE serialization

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val units = [0x41, 0xAC00, 0x4F60]
val bytes = utf16_to_bytes_be(units)
val restored = utf16_from_bytes_be(bytes)
expect(restored).to_equal(units)
```

</details>

### utf16 to utf8 cross-codec

#### converts ASCII

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val utf16_units = [0x48, 0x69]  # "Hi"
val utf8_bytes = utf16_to_utf8(utf16_units)
expect(utf8_bytes).to_equal([0x48, 0x69])
```

</details>

#### converts Korean

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 가 = U+AC00 -> UTF-8: EA B0 80
val utf16_units = [0xAC00]
val utf8_bytes = utf16_to_utf8(utf16_units)
expect(utf8_bytes.len()).to_equal(3)
expect(utf8_bytes[0]).to_equal(0xEA)
expect(utf8_bytes[1]).to_equal(0xB0)
expect(utf8_bytes[2]).to_equal(0x80)
```

</details>

#### converts emoji via surrogates

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# U+1F600 in UTF-16 = D83D DE00
val utf16_units = [0xD83D, 0xDE00]
val utf8_bytes = utf16_to_utf8(utf16_units)
expect(utf8_bytes.len()).to_equal(4)
expect(utf8_bytes[0]).to_equal(0xF0)
expect(utf8_bytes[1]).to_equal(0x9F)
expect(utf8_bytes[2]).to_equal(0x98)
expect(utf8_bytes[3]).to_equal(0x80)
```

</details>

### utf8 to utf16 cross-codec

#### converts ASCII

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val utf8_bytes = [0x48, 0x69]
val utf16_units = utf8_to_utf16(utf8_bytes)
expect(utf16_units).to_equal([0x48, 0x69])
```

</details>

#### converts Korean

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 가 = EA B0 80 -> U+AC00
val utf8_bytes = [0xEA, 0xB0, 0x80]
val utf16_units = utf8_to_utf16(utf8_bytes)
expect(utf16_units.len()).to_equal(1)
expect(utf16_units[0]).to_equal(0xAC00)
```

</details>

#### roundtrips mixed content through UTF-8

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original_cps = [0x41, 0xAC00, 0x1F600]
val utf16_units = utf16_encode_all(original_cps)
val utf8_bytes = utf16_to_utf8(utf16_units)
val back_units = utf8_to_utf16(utf8_bytes)
val result_cps = utf16_decode_all(back_units)
expect(result_cps).to_equal(original_cps)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/utf16_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- utf16_encode_one
- utf16_decode_one
- utf16_encode_all and utf16_decode_all
- utf16_to_bytes_le
- utf16_to_bytes_be
- utf16 bytes roundtrip
- utf16 to utf8 cross-codec
- utf8 to utf16 cross-codec

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
