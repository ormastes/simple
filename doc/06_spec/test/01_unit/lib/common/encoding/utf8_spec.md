# Utf8 Specification

> <details>

<!-- sdn-diagram:id=utf8_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=utf8_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

utf8_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=utf8_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 45 | 45 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Utf8 Specification

## Scenarios

### utf8_seq_len

#### returns 1 for ASCII bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(utf8_seq_len(0x00)).to_equal(1)
expect(utf8_seq_len(0x41)).to_equal(1)  # 'A'
expect(utf8_seq_len(0x7F)).to_equal(1)
```

</details>

#### returns 0 for continuation bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(utf8_seq_len(0x80)).to_equal(0)
expect(utf8_seq_len(0xBF)).to_equal(0)
```

</details>

#### returns 2 for 2-byte lead

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(utf8_seq_len(0xC0)).to_equal(2)
expect(utf8_seq_len(0xDF)).to_equal(2)
```

</details>

#### returns 3 for 3-byte lead

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(utf8_seq_len(0xE0)).to_equal(3)
expect(utf8_seq_len(0xEF)).to_equal(3)
```

</details>

#### returns 4 for 4-byte lead

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(utf8_seq_len(0xF0)).to_equal(4)
expect(utf8_seq_len(0xF7)).to_equal(4)
```

</details>

#### returns 0 for invalid lead bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(utf8_seq_len(0xF8)).to_equal(0)
expect(utf8_seq_len(0xFF)).to_equal(0)
expect(utf8_seq_len(-1)).to_equal(0)
```

</details>

### utf8_encode_one

#### encodes ASCII codepoints as single byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(utf8_encode_one(0x41)).to_equal([0x41])  # 'A'
expect(utf8_encode_one(0x00)).to_equal([0x00])
expect(utf8_encode_one(0x7F)).to_equal([0x7F])
```

</details>

#### encodes 2-byte codepoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# U+00E9 = e-acute = 0xC3 0xA9
val encoded = utf8_encode_one(0xE9)
expect(encoded.len()).to_equal(2)
expect(encoded[0]).to_equal(0xC3)
expect(encoded[1]).to_equal(0xA9)
```

</details>

#### encodes 3-byte codepoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# U+AC00 = first Hangul syllable 가 = 0xEA 0xB0 0x80
val encoded = utf8_encode_one(0xAC00)
expect(encoded.len()).to_equal(3)
expect(encoded[0]).to_equal(0xEA)
expect(encoded[1]).to_equal(0xB0)
expect(encoded[2]).to_equal(0x80)
```

</details>

#### encodes 4-byte codepoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# U+1F600 = grinning face emoji = 0xF0 0x9F 0x98 0x80
val encoded = utf8_encode_one(0x1F600)
expect(encoded.len()).to_equal(4)
expect(encoded[0]).to_equal(0xF0)
expect(encoded[1]).to_equal(0x9F)
expect(encoded[2]).to_equal(0x98)
expect(encoded[3]).to_equal(0x80)
```

</details>

#### replaces surrogates with U+FFFD

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = utf8_encode_one(0xD800)
expect(encoded).to_equal([0xEF, 0xBF, 0xBD])
```

</details>

#### replaces out-of-range with U+FFFD

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = utf8_encode_one(0x110000)
expect(encoded).to_equal([0xEF, 0xBF, 0xBD])
```

</details>

#### replaces negative with U+FFFD

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = utf8_encode_one(-1)
expect(encoded).to_equal([0xEF, 0xBF, 0xBD])
```

</details>

### utf8_decode_one

#### decodes ASCII byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = utf8_decode_one([0x41], 0)
expect(result[0]).to_equal(0x41)
expect(result[1]).to_equal(1)
```

</details>

#### decodes 2-byte sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# U+00E9 = 0xC3 0xA9
val result = utf8_decode_one([0xC3, 0xA9], 0)
expect(result[0]).to_equal(0xE9)
expect(result[1]).to_equal(2)
```

</details>

#### decodes 3-byte sequence for Korean

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# U+AC00 가 = 0xEA 0xB0 0x80
val result = utf8_decode_one([0xEA, 0xB0, 0x80], 0)
expect(result[0]).to_equal(0xAC00)
expect(result[1]).to_equal(3)
```

</details>

#### decodes 4-byte sequence for emoji

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# U+1F600 = 0xF0 0x9F 0x98 0x80
val result = utf8_decode_one([0xF0, 0x9F, 0x98, 0x80], 0)
expect(result[0]).to_equal(0x1F600)
expect(result[1]).to_equal(4)
```

</details>

#### returns replacement for continuation byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = utf8_decode_one([0x80], 0)
expect(result[0]).to_equal(0xFFFD)
expect(result[1]).to_equal(1)
```

</details>

#### returns replacement for truncated sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 3-byte lead but only 2 bytes available
val result = utf8_decode_one([0xEA, 0xB0], 0)
expect(result[0]).to_equal(0xFFFD)
expect(result[1]).to_equal(1)
```

</details>

#### rejects overlong 2-byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Overlong: U+0041 encoded as 0xC1 0x81 (should be 1 byte)
val result = utf8_decode_one([0xC1, 0x81], 0)
expect(result[0]).to_equal(0xFFFD)
expect(result[1]).to_equal(2)
```

</details>

#### returns error for out-of-bounds offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = utf8_decode_one([0x41], 5)
expect(result[0]).to_equal(-1)
expect(result[1]).to_equal(0)
```

</details>

#### decodes at nonzero offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = utf8_decode_one([0x41, 0x42, 0x43], 1)
expect(result[0]).to_equal(0x42)
expect(result[1]).to_equal(1)
```

</details>

### utf8_codepoint_byte_len

#### returns 1 for ASCII

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(utf8_codepoint_byte_len(0x41)).to_equal(1)
```

</details>

#### returns 2 for Latin extended

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(utf8_codepoint_byte_len(0xE9)).to_equal(2)
```

</details>

#### returns 3 for CJK and Hangul

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(utf8_codepoint_byte_len(0xAC00)).to_equal(3)
expect(utf8_codepoint_byte_len(0x4E00)).to_equal(3)  # CJK ideograph
```

</details>

#### returns 4 for supplementary planes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(utf8_codepoint_byte_len(0x1F600)).to_equal(4)
expect(utf8_codepoint_byte_len(0x10FFFF)).to_equal(4)
```

</details>

### utf8_encode_all and utf8_decode_all

#### roundtrips ASCII

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cps = [0x48, 0x65, 0x6C, 0x6C, 0x6F]  # "Hello"
val encoded = utf8_encode_all(cps)
val decoded = utf8_decode_all(encoded)
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
val encoded = utf8_encode_all(cps)
expect(encoded.len()).to_equal(9)  # 3 bytes each
val decoded = utf8_decode_all(encoded)
expect(decoded).to_equal(cps)
```

</details>

#### roundtrips mixed ASCII and emoji

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "Hi" + U+1F600
val cps = [0x48, 0x69, 0x1F600]
val encoded = utf8_encode_all(cps)
expect(encoded.len()).to_equal(6)  # 1+1+4
val decoded = utf8_decode_all(encoded)
expect(decoded).to_equal(cps)
```

</details>

#### roundtrips Cyrillic

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Привет = U+041F U+0440 U+0438 U+0432 U+0435 U+0442
val cps = [0x041F, 0x0440, 0x0438, 0x0432, 0x0435, 0x0442]
val encoded = utf8_encode_all(cps)
val decoded = utf8_decode_all(encoded)
expect(decoded).to_equal(cps)
```

</details>

#### roundtrips Arabic

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# مرحبا = U+0645 U+0631 U+062D U+0628 U+0627
val cps = [0x0645, 0x0631, 0x062D, 0x0628, 0x0627]
val encoded = utf8_encode_all(cps)
val decoded = utf8_decode_all(encoded)
expect(decoded).to_equal(cps)
```

</details>

#### roundtrips Japanese Hiragana

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# こんにちは = U+3053 U+3093 U+306B U+3061 U+306F
val cps = [0x3053, 0x3093, 0x306B, 0x3061, 0x306F]
val encoded = utf8_encode_all(cps)
val decoded = utf8_decode_all(encoded)
expect(decoded).to_equal(cps)
```

</details>

#### roundtrips Chinese

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 你好 = U+4F60 U+597D
val cps = [0x4F60, 0x597D]
val encoded = utf8_encode_all(cps)
expect(encoded.len()).to_equal(6)  # 3 bytes each
val decoded = utf8_decode_all(encoded)
expect(decoded).to_equal(cps)
```

</details>

#### roundtrips Devanagari

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# नमस्ते = U+0928 U+092E U+0938 U+094D U+0924 U+0947
val cps = [0x0928, 0x092E, 0x0938, 0x094D, 0x0924, 0x0947]
val encoded = utf8_encode_all(cps)
val decoded = utf8_decode_all(encoded)
expect(decoded).to_equal(cps)
```

</details>

#### handles empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = utf8_encode_all([])
expect(encoded.len()).to_equal(0)
val decoded = utf8_decode_all([])
expect(decoded.len()).to_equal(0)
```

</details>

### codepoint counting via decode_all

#### counts ASCII bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decoded = utf8_decode_all([0x48, 0x65, 0x6C, 0x6C, 0x6F])
expect(decoded.len()).to_equal(5)
```

</details>

#### counts Korean 3-byte sequences

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = utf8_encode_all([0xAC00, 0xB098, 0xB2E4])
val decoded = utf8_decode_all(bytes)
expect(decoded.len()).to_equal(3)
```

</details>

#### counts emoji 4-byte sequences

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = utf8_encode_all([0x1F600, 0x1F601])
val decoded = utf8_decode_all(bytes)
expect(decoded.len()).to_equal(2)
```

</details>

#### counts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decoded = utf8_decode_all([])
expect(decoded.len()).to_equal(0)
```

</details>

### text_byte_len

#### returns byte length of ASCII text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_byte_len("Hello")).to_equal(5)
```

</details>

#### returns byte length of empty text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_byte_len("")).to_equal(0)
```

</details>

### text_codepoints length

#### returns codepoint count for ASCII

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cps = text_codepoints("Hello")
expect(cps.len()).to_equal(5)
```

</details>

### text_codepoints

#### returns codepoints for ASCII

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cps = text_codepoints("ABC")
expect(cps.len()).to_equal(3)
expect(cps[0]).to_equal(0x41)
expect(cps[1]).to_equal(0x42)
expect(cps[2]).to_equal(0x43)
```

</details>

### char_from_codepoint

#### converts ASCII codepoint to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_codepoint(0x41)).to_equal("A")
expect(char_from_codepoint(0x30)).to_equal("0")
```

</details>

### text_from_codepoints

#### creates text from ASCII codepoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = text_from_codepoints([0x48, 0x69])
expect(result).to_equal("Hi")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/utf8_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- utf8_seq_len
- utf8_encode_one
- utf8_decode_one
- utf8_codepoint_byte_len
- utf8_encode_all and utf8_decode_all
- codepoint counting via decode_all
- text_byte_len
- text_codepoints length
- text_codepoints
- char_from_codepoint
- text_from_codepoints

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 45 |
| Active scenarios | 45 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
