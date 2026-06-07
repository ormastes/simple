# String Codec Specification

> <details>

<!-- sdn-diagram:id=string_codec_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=string_codec_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

string_codec_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=string_codec_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Codec Specification

## Scenarios

### HPACK string codec — encoder

#### encodes the empty string as a single zero byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = encode_string_octets_raw([])
expect(out.len()).to_equal(1)
expect(out[0]).to_equal(0x00u8)
```

</details>

#### encodes a 10-byte string with the H=0 length prefix (RFC 7541 C.2.1 name)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "custom-key" is 10 bytes; H=0, length fits in 7-bit prefix → 0x0a header.
val key = _custom_key_bytes()
val out = encode_string_octets_raw(key)
expect(out.len()).to_equal(11)
expect(out[0]).to_equal(0x0au8)
# Verify the first and last payload bytes match the source.
expect(out[1]).to_equal(0x63u8)
expect(out[10]).to_equal(0x79u8)
```

</details>

#### encodes a 13-byte string (RFC 7541 C.2.1 value)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = _custom_header_bytes()
val out = encode_string_octets_raw(value)
expect(out.len()).to_equal(14)
expect(out[0]).to_equal(0x0du8)
expect(out[1]).to_equal(0x63u8)
expect(out[13]).to_equal(0x72u8)
```

</details>

#### encodes a 127-byte string in a single header byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 127 == 2^7 - 1 boundary; needs the multi-byte form (one continuation 0).
val payload = _make_repeating(0x41u8, 127)
val out = encode_string_octets_raw(payload)
# 127 == mask, so prefix = 0x7f, then continuation 0x00, then 127 bytes.
expect(out.len()).to_equal(2 + 127)
expect(out[0]).to_equal(0x7fu8)
expect(out[1]).to_equal(0x00u8)
```

</details>

### HPACK string codec — decoder

#### decodes the empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = decode_string_octets_raw([0x00u8], 0)
expect(res.is_ok()).to_equal(true)
val pair = res.unwrap()
expect(pair.0.len()).to_equal(0)
expect(pair.1).to_equal(1)
```

</details>

#### decodes the RFC 7541 C.2.1 'custom-key' field

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Header 0x0a + 10 ASCII bytes for "custom-key".
val header: [u8] = [0x0au8]
val bytes = header + _custom_key_bytes()
val res = decode_string_octets_raw(bytes, 0)
expect(res.is_ok()).to_equal(true)
val pair = res.unwrap()
expect(pair.0.len()).to_equal(10)
expect(pair.0[0]).to_equal(0x63u8)
expect(pair.0[9]).to_equal(0x79u8)
expect(pair.1).to_equal(11)
```

</details>

#### rejects Huffman-coded strings (H=1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Header 0x80 (H=1, length prefix 0). Rejected per §5.2.
val res = decode_string_octets_raw([0x80u8], 0)
expect(res.is_err()).to_equal(true)
```

</details>

#### rejects truncated payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Header says 10 bytes, but only 3 bytes follow.
val res = decode_string_octets_raw([0x0au8, 0x61u8, 0x62u8, 0x63u8], 0)
expect(res.is_err()).to_equal(true)
```

</details>

#### rejects out-of-range offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = decode_string_octets_raw([0x00u8], 5)
expect(res.is_err()).to_equal(true)
```

</details>

#### tolerates trailing bytes after the string (returns consumed count)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Encode "abc" with one trailing 0xFF.
val bytes: [u8] = [0x03u8, 0x61u8, 0x62u8, 0x63u8, 0xffu8]
val res = decode_string_octets_raw(bytes, 0)
expect(res.is_ok()).to_equal(true)
val pair = res.unwrap()
expect(pair.0.len()).to_equal(3)
expect(pair.1).to_equal(4)
```

</details>

### HPACK string codec — round-trip

#### round-trips empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_string_octets_raw([])
val decoded = decode_string_octets_raw(encoded, 0).unwrap()
expect(decoded.0.len()).to_equal(0)
```

</details>

#### round-trips short ASCII

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _custom_key_bytes()
val encoded = encode_string_octets_raw(key)
val decoded = decode_string_octets_raw(encoded, 0).unwrap()
expect(decoded.0.len()).to_equal(10)
var i: i64 = 0
var ok = true
while i < 10:
    if decoded.0[i] != key[i]:
        ok = false
    i = i + 1
expect(ok).to_equal(true)
```

</details>

#### round-trips 200-byte payload (multi-byte length)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _make_indexed(200)
val encoded = encode_string_octets_raw(payload)
val decoded = decode_string_octets_raw(encoded, 0).unwrap()
expect(decoded.0.len()).to_equal(200)
# Spot-check first, middle, last
expect(decoded.0[0]).to_equal(0x00u8)
expect(decoded.0[100]).to_equal(0x64u8)
expect(decoded.0[199]).to_equal(0xc7u8)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/hpack/string_codec_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HPACK string codec — encoder
- HPACK string codec — decoder
- HPACK string codec — round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
