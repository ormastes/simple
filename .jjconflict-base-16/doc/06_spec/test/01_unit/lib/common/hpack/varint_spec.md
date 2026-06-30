# Varint Specification

> <details>

<!-- sdn-diagram:id=varint_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=varint_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

varint_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=varint_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Varint Specification

## Scenarios

### HPACK varint encoder

#### encodes a small value (10) in a 5-bit prefix as a single byte (RFC 7541 C.1.1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Value 10 fits in 5 bits (since 10 < 31). Prefix carries it directly.
# No flag bits; first byte = 0x0a.
val out = encode_prefix_int(10, 5, 0x00u8)
expect(out.len()).to_equal(1)
expect(out[0]).to_equal(0x0au8)
```

</details>

#### encodes 1337 in a 5-bit prefix using continuation bytes (RFC 7541 C.1.2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 1337 >= 31, so prefix = 11111 (mask=31), remainder = 1306.
# 1306 = 154 * 1 + 9 * 128 → continuation bytes 154|128, 9 → 0x9a, 0x0a.
# Final encoding: [0x1f, 0x9a, 0x0a].
val out = encode_prefix_int(1337, 5, 0x00u8)
expect(out.len()).to_equal(3)
expect(out[0]).to_equal(0x1fu8)
expect(out[1]).to_equal(0x9au8)
expect(out[2]).to_equal(0x0au8)
```

</details>

#### encodes 42 in an 8-bit prefix (RFC 7541 C.1.3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 42 fits directly in 8 bits.
val out = encode_prefix_int(42, 8, 0x00u8)
expect(out.len()).to_equal(1)
expect(out[0]).to_equal(0x2au8)
```

</details>

#### encodes the boundary value (mask) using one continuation byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# In 5-bit prefix, value 31 == mask, so prefix=0x1f and one
# continuation byte 0x00.
val out = encode_prefix_int(31, 5, 0x00u8)
expect(out.len()).to_equal(2)
expect(out[0]).to_equal(0x1fu8)
expect(out[1]).to_equal(0x00u8)
```

</details>

#### preserves the flag bits in the first byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 7-bit prefix (mask=127), value 10, flag 0x80 (Indexed Header Field).
val out = encode_prefix_int(10, 7, 0x80u8)
expect(out[0]).to_equal(0x8au8)
```

</details>

#### encodes zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = encode_prefix_int(0, 5, 0x00u8)
expect(out.len()).to_equal(1)
expect(out[0]).to_equal(0x00u8)
```

</details>

### HPACK varint decoder

#### decodes the C.1.1 example back to 10

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [u8] = [0x0au8]
val res = decode_prefix_int(bytes, 0, 5)
expect(res.is_ok()).to_equal(true)
val pair = res.unwrap()
expect(pair.0).to_equal(10)
expect(pair.1).to_equal(1)
```

</details>

#### decodes the C.1.2 example back to 1337

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [u8] = [0x1fu8, 0x9au8, 0x0au8]
val res = decode_prefix_int(bytes, 0, 5)
expect(res.is_ok()).to_equal(true)
val pair = res.unwrap()
expect(pair.0).to_equal(1337)
expect(pair.1).to_equal(3)
```

</details>

#### decodes the C.1.3 example back to 42

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [u8] = [0x2au8]
val res = decode_prefix_int(bytes, 0, 8)
expect(res.is_ok()).to_equal(true)
val pair = res.unwrap()
expect(pair.0).to_equal(42)
expect(pair.1).to_equal(1)
```

</details>

#### ignores high flag bits when decoding

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 7-bit prefix; first byte 0x8a (flag=0x80, value=10).
val bytes: [u8] = [0x8au8]
val res = decode_prefix_int(bytes, 0, 7)
expect(res.is_ok()).to_equal(true)
expect(res.unwrap().0).to_equal(10)
```

</details>

#### rejects truncated continuation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 5-bit prefix says continue (0x1f), but no continuation byte present.
val bytes: [u8] = [0x1fu8]
val res = decode_prefix_int(bytes, 0, 5)
expect(res.is_err()).to_equal(true)
```

</details>

#### rejects out-of-range offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [u8] = [0x0au8]
val res = decode_prefix_int(bytes, 5, 5)
expect(res.is_err()).to_equal(true)
```

</details>

#### round-trips large values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 12345678 > 31, far beyond single-byte form.
val encoded = encode_prefix_int(12345678, 5, 0x00u8)
val res = decode_prefix_int(encoded, 0, 5)
expect(res.is_ok()).to_equal(true)
expect(res.unwrap().0).to_equal(12345678)
expect(res.unwrap().1).to_equal(encoded.len())
```

</details>

#### round-trips zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_prefix_int(0, 7, 0x80u8)
val res = decode_prefix_int(encoded, 0, 7)
expect(res.unwrap().0).to_equal(0)
```

</details>

### HPACK varint round-trip across all prefix widths

#### round-trips a sample value through prefixes 4..8

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample: i64 = 200
val enc4 = encode_prefix_int(sample, 4, 0x00u8)
val enc5 = encode_prefix_int(sample, 5, 0x00u8)
val enc6 = encode_prefix_int(sample, 6, 0x00u8)
val enc7 = encode_prefix_int(sample, 7, 0x00u8)
val enc8 = encode_prefix_int(sample, 8, 0x00u8)
expect(decode_prefix_int(enc4, 0, 4).unwrap().0).to_equal(sample)
expect(decode_prefix_int(enc5, 0, 5).unwrap().0).to_equal(sample)
expect(decode_prefix_int(enc6, 0, 6).unwrap().0).to_equal(sample)
expect(decode_prefix_int(enc7, 0, 7).unwrap().0).to_equal(sample)
expect(decode_prefix_int(enc8, 0, 8).unwrap().0).to_equal(sample)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/hpack/varint_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HPACK varint encoder
- HPACK varint decoder
- HPACK varint round-trip across all prefix widths

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
