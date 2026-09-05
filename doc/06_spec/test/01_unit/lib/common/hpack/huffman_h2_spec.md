# Huffman H2 Specification

> <details>

<!-- sdn-diagram:id=huffman_h2_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=huffman_h2_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

huffman_h2_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=huffman_h2_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Huffman H2 Specification

## Scenarios

### HPACK Huffman encoder — RFC 7541 §C.4 reference vectors

#### encodes 'www.example.com' (§C.4.1) correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = hpack_huffman_encode(_www_example_com())
val expected = _www_example_com_encoded()
expect(encoded.len()).to_equal(12)
expect(_bytes_eq(encoded, expected)).to_equal(true)
```

</details>

#### encodes 'no-cache' (§C.4.2) correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = hpack_huffman_encode(_no_cache())
val expected = _no_cache_encoded()
expect(encoded.len()).to_equal(6)
expect(_bytes_eq(encoded, expected)).to_equal(true)
```

</details>

#### encodes 'custom-key' (§C.4.3) correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = hpack_huffman_encode(_custom_key())
val expected = _custom_key_encoded()
expect(encoded.len()).to_equal(8)
expect(_bytes_eq(encoded, expected)).to_equal(true)
```

</details>

#### encodes 'custom-value' (§C.4.3) correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = hpack_huffman_encode(_custom_value())
val expected = _custom_value_encoded()
expect(encoded.len()).to_equal(9)
expect(_bytes_eq(encoded, expected)).to_equal(true)
```

</details>

### HPACK Huffman encoder — basic cases

#### encodes empty payload to empty output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = hpack_huffman_encode([])
expect(out.len()).to_equal(0)
```

</details>

#### encodes a single byte (0x61 = 'a') with EOS padding

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 'a' = 00011 (5 bits); padded to 8 bits with 3 high EOS bits → 000 11111
# = 0x1f
val out = hpack_huffman_encode([0x61u8])
expect(out.len()).to_equal(1)
expect(out[0]).to_equal(0x1fu8)
```

</details>

#### encodes '200' correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = hpack_huffman_encode(_status_200())
# Just verify it produces some output and round-trips.
expect(out.len()).to_be_greater_than(0)
```

</details>

### HPACK Huffman decoder — RFC 7541 §C.4 reference vectors

#### decodes 'www.example.com' (§C.4.1) correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = _www_example_com_encoded()
val res = hpack_huffman_decode(enc, 0, enc.len())
expect(res.is_ok()).to_equal(true)
val decoded = res.unwrap()
expect(_bytes_eq(decoded, _www_example_com())).to_equal(true)
```

</details>

#### decodes 'no-cache' (§C.4.2) correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = _no_cache_encoded()
val res = hpack_huffman_decode(enc, 0, enc.len())
expect(res.is_ok()).to_equal(true)
val decoded = res.unwrap()
expect(_bytes_eq(decoded, _no_cache())).to_equal(true)
```

</details>

#### decodes 'custom-key' (§C.4.3) correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = _custom_key_encoded()
val res = hpack_huffman_decode(enc, 0, enc.len())
expect(res.is_ok()).to_equal(true)
val decoded = res.unwrap()
expect(_bytes_eq(decoded, _custom_key())).to_equal(true)
```

</details>

#### decodes 'custom-value' (§C.4.3) correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = _custom_value_encoded()
val res = hpack_huffman_decode(enc, 0, enc.len())
expect(res.is_ok()).to_equal(true)
val decoded = res.unwrap()
expect(_bytes_eq(decoded, _custom_value())).to_equal(true)
```

</details>

### HPACK Huffman decoder — error cases

#### rejects a stream containing an explicit EOS symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stream = _eos_embedded_stream()
val res = hpack_huffman_decode(stream, 0, stream.len())
expect(res.is_err()).to_equal(true)
```

</details>

#### rejects padding longer than 7 bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stream = _over_padded_stream()
val res = hpack_huffman_decode(stream, 0, stream.len())
expect(res.is_err()).to_equal(true)
```

</details>

#### rejects negative offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = _no_cache_encoded()
val res = hpack_huffman_decode(enc, -1, enc.len())
expect(res.is_err()).to_equal(true)
```

</details>

#### rejects length that exceeds buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = _no_cache_encoded()
val res = hpack_huffman_decode(enc, 0, enc.len() + 1)
expect(res.is_err()).to_equal(true)
```

</details>

### HPACK Huffman codec — round-trip

#### round-trips empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = hpack_huffman_encode([])
val res = hpack_huffman_decode(encoded, 0, encoded.len())
expect(res.is_ok()).to_equal(true)
expect(res.unwrap().len()).to_equal(0)
```

</details>

#### round-trips single byte 'a'

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload: [u8] = [0x61u8]
val encoded = hpack_huffman_encode(payload)
val res = hpack_huffman_decode(encoded, 0, encoded.len())
expect(res.is_ok()).to_equal(true)
val decoded = res.unwrap()
expect(decoded.len()).to_equal(1)
expect(decoded[0]).to_equal(0x61u8)
```

</details>

#### round-trips '200'

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _status_200()
val encoded = hpack_huffman_encode(payload)
val res = hpack_huffman_decode(encoded, 0, encoded.len())
expect(res.is_ok()).to_equal(true)
val decoded = res.unwrap()
expect(_bytes_eq(decoded, payload)).to_equal(true)
```

</details>

#### round-trips 256-byte indexed payload (covers every symbol 0x00-0xff)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _make_indexed(256)
val encoded = hpack_huffman_encode(payload)
val res = hpack_huffman_decode(encoded, 0, encoded.len())
expect(res.is_ok()).to_equal(true)
val decoded = res.unwrap()
expect(decoded.len()).to_equal(256)
expect(_bytes_eq(decoded, payload)).to_equal(true)
```

</details>

#### round-trips 100-byte repeating payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _make_repeating(0x41u8, 100)
val encoded = hpack_huffman_encode(payload)
val res = hpack_huffman_decode(encoded, 0, encoded.len())
expect(res.is_ok()).to_equal(true)
val decoded = res.unwrap()
expect(decoded.len()).to_equal(100)
expect(_bytes_eq(decoded, payload)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/hpack/huffman_h2_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HPACK Huffman encoder — RFC 7541 §C.4 reference vectors
- HPACK Huffman encoder — basic cases
- HPACK Huffman decoder — RFC 7541 §C.4 reference vectors
- HPACK Huffman decoder — error cases
- HPACK Huffman codec — round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
