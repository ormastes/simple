# HPACK Huffman Correctness and Decode/Encode Coverage

> Comprehensive tests for `src/lib/nogc_async_mut/http/h2/hpack_huffman.spl`.

<!-- sdn-diagram:id=hpack_huffman_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hpack_huffman_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hpack_huffman_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hpack_huffman_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HPACK Huffman Correctness and Decode/Encode Coverage

Comprehensive tests for `src/lib/nogc_async_mut/http/h2/hpack_huffman.spl`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #HTTP2-HUFFMAN-001 |
| Category | Stdlib / HTTP/2 / HPACK Huffman |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/lib/nogc_async_mut/http/h2/hpack_huffman_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Comprehensive tests for `src/lib/nogc_async_mut/http/h2/hpack_huffman.spl`.
Covers round-trip correctness, RFC 7541 Appendix B/C.4 test vectors,
edge cases (empty, single char, all-padding, max-length), error handling
(truncated/invalid sequences), padding validation, and compression ratio.

## Scenarios

### HPACK Huffman encoder — RFC 7541 C.4 vectors

#### encodes 'www.example.com' to RFC C.4.1 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = hpack_huffman_encode(www_example_com_bytes())
expect(encoded.len()).to_equal(12)
expect(bytes_eq(encoded, www_example_com_huffman())).to_equal(true)
```

</details>

#### encodes 'no-cache' to RFC C.4.2 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = hpack_huffman_encode(no_cache_bytes())
expect(encoded.len()).to_equal(6)
expect(bytes_eq(encoded, no_cache_huffman())).to_equal(true)
```

</details>

#### encodes 'custom-key' to RFC C.4.3 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = hpack_huffman_encode(custom_key_bytes())
expect(encoded.len()).to_equal(8)
expect(bytes_eq(encoded, custom_key_huffman())).to_equal(true)
```

</details>

#### encodes 'custom-value' to RFC C.4.3 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = hpack_huffman_encode(custom_value_bytes())
expect(encoded.len()).to_equal(9)
expect(bytes_eq(encoded, custom_value_huffman())).to_equal(true)
```

</details>

### HPACK Huffman encoder — basic cases

#### encodes empty input to empty output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = hpack_huffman_encode([])
expect(out.len()).to_equal(0)
```

</details>

#### encodes single byte 0x61 ('a') with EOS padding

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 'a' = code 0x00011, 5 bits → padded to 8 bits: 00011 111 = 0x1f
val out = hpack_huffman_encode([0x61])
expect(out.len()).to_equal(1)
expect(out[0]).to_equal(0x1f)
```

</details>

#### encodes single byte 0x30 ('0') correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# '0' = code 0x00, 5 bits → padded to 8 bits: 00000 111 = 0x07
val out = hpack_huffman_encode([0x30])
expect(out.len()).to_equal(1)
expect(out[0]).to_equal(0x07)
```

</details>

#### padding bits are all 1s (EOS prefix)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# For any single-char encode, the trailing pad bits must be 1s.
# 'e' = code 00100, 5 bits → 00100 111 = 0x27
val out = hpack_huffman_encode([0x65])
expect(out.len()).to_equal(1)
# Verify the low 3 bits (padding) are all 1
val pad = out[0] & 0x07
expect(pad).to_equal(0x07)
```

</details>

### HPACK Huffman decoder — RFC 7541 C.4 vectors

#### decodes 'www.example.com' (C.4.1) correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = www_example_com_huffman()
val decoded = hpack_huffman_decode(enc, enc.len() * 8)
expect(bytes_eq(decoded, www_example_com_bytes())).to_equal(true)
```

</details>

#### decodes 'no-cache' (C.4.2) correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = no_cache_huffman()
val decoded = hpack_huffman_decode(enc, enc.len() * 8)
expect(bytes_eq(decoded, no_cache_bytes())).to_equal(true)
```

</details>

#### decodes 'custom-key' (C.4.3) correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = custom_key_huffman()
val decoded = hpack_huffman_decode(enc, enc.len() * 8)
expect(bytes_eq(decoded, custom_key_bytes())).to_equal(true)
```

</details>

#### decodes 'custom-value' (C.4.3) correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = custom_value_huffman()
val decoded = hpack_huffman_decode(enc, enc.len() * 8)
expect(bytes_eq(decoded, custom_value_bytes())).to_equal(true)
```

</details>

### HPACK Huffman decoder — edge cases

#### decodes empty input to empty output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decoded = hpack_huffman_decode([], 0)
expect(decoded.len()).to_equal(0)
```

</details>

#### decodes with zero bit_count returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = no_cache_huffman()
val decoded = hpack_huffman_decode(enc, 0)
expect(decoded.len()).to_equal(0)
```

</details>

#### truncated input returns partial decode (not crash)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Take first 3 bytes of www.example.com encoding (12 bytes total)
# Decode should produce some output without crashing
val full = www_example_com_huffman()
var truncated: [u8] = [full[0], full[1], full[2]]
val decoded = hpack_huffman_decode(truncated, truncated.len() * 8)
# Should produce fewer characters than the full 15-char original
expect(decoded.len()).to_be_less_than(15)
```

</details>

#### single all-1s byte (pure padding) decodes to empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0xff = 8 bits of 1s. This is valid padding only (no complete symbol
# starts with all 1s at lengths <= 8). Decoder should produce empty.
val decoded = hpack_huffman_decode([0xff], 8)
expect(decoded.len()).to_equal(0)
```

</details>

### HPACK Huffman round-trip

#### round-trips empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = hpack_huffman_encode([])
val decoded = hpack_huffman_decode(encoded, encoded.len() * 8)
expect(decoded.len()).to_equal(0)
```

</details>

#### round-trips single byte 'a' (0x61)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload: [u8] = [0x61]
val encoded = hpack_huffman_encode(payload)
val decoded = hpack_huffman_decode(encoded, encoded.len() * 8)
expect(decoded.len()).to_equal(1)
expect(decoded[0]).to_equal(0x61)
```

</details>

#### round-trips 'content-type'

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = str_to_bytes("content-type")
val encoded = hpack_huffman_encode(payload)
val decoded = hpack_huffman_decode(encoded, encoded.len() * 8)
expect(bytes_eq(decoded, payload)).to_equal(true)
```

</details>

#### round-trips 'GET'

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = str_to_bytes("GET")
val encoded = hpack_huffman_encode(payload)
val decoded = hpack_huffman_decode(encoded, encoded.len() * 8)
expect(bytes_eq(decoded, payload)).to_equal(true)
```

</details>

#### round-trips '/index.html'

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = str_to_bytes("/index.html")
val encoded = hpack_huffman_encode(payload)
val decoded = hpack_huffman_decode(encoded, encoded.len() * 8)
expect(bytes_eq(decoded, payload)).to_equal(true)
```

</details>

#### round-trips 'www.example.com'

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = www_example_com_bytes()
val encoded = hpack_huffman_encode(payload)
val decoded = hpack_huffman_decode(encoded, encoded.len() * 8)
expect(bytes_eq(decoded, payload)).to_equal(true)
```

</details>

#### round-trips 'no-cache'

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = no_cache_bytes()
val encoded = hpack_huffman_encode(payload)
val decoded = hpack_huffman_decode(encoded, encoded.len() * 8)
expect(bytes_eq(decoded, payload)).to_equal(true)
```

</details>

#### round-trips 100-byte repeating payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = make_repeating(0x41, 100)
val encoded = hpack_huffman_encode(payload)
val decoded = hpack_huffman_decode(encoded, encoded.len() * 8)
expect(decoded.len()).to_equal(100)
expect(bytes_eq(decoded, payload)).to_equal(true)
```

</details>

#### round-trips 64-byte indexed payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = make_indexed(64)
val encoded = hpack_huffman_encode(payload)
val decoded = hpack_huffman_decode(encoded, encoded.len() * 8)
expect(decoded.len()).to_equal(64)
expect(bytes_eq(decoded, payload)).to_equal(true)
```

</details>

#### round-trips 128-byte indexed payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = make_indexed(128)
val encoded = hpack_huffman_encode(payload)
val decoded = hpack_huffman_decode(encoded, encoded.len() * 8)
expect(decoded.len()).to_equal(128)
expect(bytes_eq(decoded, payload)).to_equal(true)
```

</details>

#### round-trips 256-byte indexed payload (all symbols 0x00-0xff)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = make_indexed(256)
val encoded = hpack_huffman_encode(payload)
val decoded = hpack_huffman_decode(encoded, encoded.len() * 8)
expect(decoded.len()).to_equal(256)
expect(bytes_eq(decoded, payload)).to_equal(true)
```

</details>

#### round-trips 10-byte mixed payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var payload: [u8] = [0x00, 0x41, 0x61, 0x7a, 0x2f, 0x3a, 0x20, 0x0d, 0x0a, 0xff]
val encoded = hpack_huffman_encode(payload)
val decoded = hpack_huffman_decode(encoded, encoded.len() * 8)
expect(decoded.len()).to_equal(10)
expect(bytes_eq(decoded, payload)).to_equal(true)
```

</details>

### HPACK Huffman encoded length

#### encoded_length matches actual encode output length

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = www_example_com_bytes()
val predicted = hpack_huffman_encoded_length(payload)
val enc = hpack_huffman_encode(payload)
val actual = enc.len()
expect(predicted).to_equal(actual)
```

</details>

#### encoded_length of empty input is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val predicted = hpack_huffman_encoded_length([])
expect(predicted).to_equal(0)
```

</details>

#### encoded_length of single 'a' is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val predicted = hpack_huffman_encoded_length([0x61])
expect(predicted).to_equal(1)
```

</details>

#### typical HTTP text compresses (output <= input length)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Common HTTP header values should compress or stay same size
val payload = str_to_bytes("text/html; charset=utf-8")
val enc_len = hpack_huffman_encoded_length(payload)
expect(enc_len <= payload.len()).to_equal(true)
```

</details>

#### Huffman encoding of 'www.example.com' saves space

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = www_example_com_bytes()
val enc_len = hpack_huffman_encoded_length(payload)
# 15 ASCII bytes → 12 Huffman bytes
expect(enc_len).to_equal(12)
expect(enc_len).to_be_less_than(payload.len())
```

</details>

#### encoded_length matches for 'no-cache'

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = no_cache_bytes()
val predicted = hpack_huffman_encoded_length(payload)
val enc = hpack_huffman_encode(payload)
val actual = enc.len()
expect(predicted).to_equal(actual)
expect(predicted).to_equal(6)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
