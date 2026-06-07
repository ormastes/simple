# Codec Specification

> <details>

<!-- sdn-diagram:id=codec_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=codec_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

codec_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=codec_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Codec Specification

## Scenarios

### codec encode and decode UTF-8

#### roundtrips ASCII text through UTF-8

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "Hello"
val bytes = encode(original, Encoding.Utf8)
val restored = decode(bytes, Encoding.Utf8)
expect(restored).to_equal(original)
```

</details>

#### encodes ASCII as identity bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = encode("Hi", Encoding.Utf8)
expect(bytes.len()).to_equal(2)
expect(bytes[0]).to_equal(0x48)
expect(bytes[1]).to_equal(0x69)
```

</details>

### codec encode and decode UTF-16LE

#### roundtrips ASCII text through UTF-16LE

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "Hello"
val bytes = encode(original, Encoding.Utf16LE)
val restored = decode(bytes, Encoding.Utf16LE)
expect(restored).to_equal(original)
```

</details>

#### UTF-16LE uses 2 bytes per ASCII char

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = encode("A", Encoding.Utf16LE)
expect(bytes.len()).to_equal(2)
expect(bytes[0]).to_equal(0x41)
expect(bytes[1]).to_equal(0x00)
```

</details>

### codec encode and decode UTF-16BE

#### roundtrips ASCII text through UTF-16BE

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "Hello"
val bytes = encode(original, Encoding.Utf16BE)
val restored = decode(bytes, Encoding.Utf16BE)
expect(restored).to_equal(original)
```

</details>

#### UTF-16BE byte order is big-endian

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = encode("A", Encoding.Utf16BE)
expect(bytes.len()).to_equal(2)
expect(bytes[0]).to_equal(0x00)
expect(bytes[1]).to_equal(0x41)
```

</details>

### codec encode and decode UTF-32LE

#### roundtrips ASCII text through UTF-32LE

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "Hello"
val bytes = encode(original, Encoding.Utf32LE)
val restored = decode(bytes, Encoding.Utf32LE)
expect(restored).to_equal(original)
```

</details>

#### UTF-32LE uses 4 bytes per char

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = encode("A", Encoding.Utf32LE)
expect(bytes.len()).to_equal(4)
expect(bytes[0]).to_equal(0x41)
expect(bytes[1]).to_equal(0x00)
expect(bytes[2]).to_equal(0x00)
expect(bytes[3]).to_equal(0x00)
```

</details>

### codec encode and decode UTF-32BE

#### roundtrips ASCII text through UTF-32BE

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "Hello"
val bytes = encode(original, Encoding.Utf32BE)
val restored = decode(bytes, Encoding.Utf32BE)
expect(restored).to_equal(original)
```

</details>

### codec encode and decode ASCII

#### roundtrips ASCII text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "Hello"
val bytes = encode(original, Encoding.Ascii)
val restored = decode(bytes, Encoding.Ascii)
expect(restored).to_equal(original)
```

</details>

#### ASCII encode is identity for 7-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = encode("ABC", Encoding.Ascii)
expect(bytes.len()).to_equal(3)
expect(bytes[0]).to_equal(0x41)
```

</details>

### codec encode and decode Latin1

#### roundtrips ASCII subset through Latin-1

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "Hello"
val bytes = encode(original, Encoding.Latin1)
val restored = decode(bytes, Encoding.Latin1)
expect(restored).to_equal(original)
```

</details>

### codec transcode

#### transcodes UTF-8 to UTF-16LE and back

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val utf8_bytes = encode("Hello", Encoding.Utf8)
val utf16_bytes = transcode(utf8_bytes, Encoding.Utf8, Encoding.Utf16LE)
val back = transcode(utf16_bytes, Encoding.Utf16LE, Encoding.Utf8)
val result = decode(back, Encoding.Utf8)
expect(result).to_equal("Hello")
```

</details>

#### transcodes UTF-8 to UTF-32BE

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val utf8_bytes = encode("A", Encoding.Utf8)
val utf32_bytes = transcode(utf8_bytes, Encoding.Utf8, Encoding.Utf32BE)
expect(utf32_bytes.len()).to_equal(4)
expect(utf32_bytes[3]).to_equal(0x41)
```

</details>

#### transcodes UTF-16LE to UTF-32LE

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val utf16_bytes = encode("A", Encoding.Utf16LE)
val utf32_bytes = transcode(utf16_bytes, Encoding.Utf16LE, Encoding.Utf32LE)
expect(utf32_bytes.len()).to_equal(4)
expect(utf32_bytes[0]).to_equal(0x41)
```

</details>

### codec edge cases

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = encode("", Encoding.Utf8)
expect(bytes.len()).to_equal(0)
val restored = decode(bytes, Encoding.Utf8)
expect(restored).to_equal("")
```

</details>

#### handles empty UTF-16LE

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = encode("", Encoding.Utf16LE)
expect(bytes.len()).to_equal(0)
```

</details>

#### handles empty UTF-32LE

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = encode("", Encoding.Utf32LE)
expect(bytes.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/codec_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- codec encode and decode UTF-8
- codec encode and decode UTF-16LE
- codec encode and decode UTF-16BE
- codec encode and decode UTF-32LE
- codec encode and decode UTF-32BE
- codec encode and decode ASCII
- codec encode and decode Latin1
- codec transcode
- codec edge cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
