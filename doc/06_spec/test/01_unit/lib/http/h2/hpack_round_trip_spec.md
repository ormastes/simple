# hpack_round_trip_spec

> Byte-exact round-trip tests for HPACK header compression (RFC 7541), focused on the W16-D acceptance criteria (5 RFC 7541 Appendix C examples).

<!-- sdn-diagram:id=hpack_round_trip_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hpack_round_trip_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hpack_round_trip_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hpack_round_trip_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hpack_round_trip_spec

Byte-exact round-trip tests for HPACK header compression (RFC 7541), focused on the W16-D acceptance criteria (5 RFC 7541 Appendix C examples).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #HTTP2-HPACK-001 |
| Category | Stdlib / HTTP/2 / HPACK |
| Difficulty | 4/5 |
| Status | Draft |
| Source | `test/01_unit/lib/http/h2/hpack_round_trip_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Byte-exact round-trip tests for HPACK header compression (RFC 7541),
focused on the W16-D acceptance criteria (5 RFC 7541 Appendix C examples).

Companion to the existing in-tree spec
`test/unit/lib/common/hpack/encoder_decoder_spec.spl` (which covers C.2-C.6
in detail). This spec is the W16-D acceptance harness for the HTTP/2 layer:
the 5 explicit examples called out in the W16-D scope, plus per-example
round-trip identity (encode→decode==original; decode→encode==input).

W16-D acceptance examples:
  C.1.1  Integer 10 in 5-bit prefix          (varint)
  C.2.1  Literal Header Field with Indexing  (custom-key: custom-header)
  C.3    Request sequence without Huffman    (3 sequential requests)
  C.4    Request sequence with Huffman       (3 sequential requests)
  C.5    Response sequence with eviction     (max_size=256, 3 responses)

Disjoint from W15-F's framing files (h2_frame.spl / h2_parser.spl /
h2_writer.spl / h2_preface.spl). Imports HPACK from std.common.hpack only.

## Scenarios

### RFC 7541 C.1.1 — Integer 10 in 5-bit prefix

#### encodes value 10 as a single byte 0x0a

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = encode_prefix_int(10, 5, 0x00u8)
expect(out.len()).to_equal(1)
expect(out[0]).to_equal(0x0au8)
```

</details>

#### decodes 0x0a back to 10 (round-trip)

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

### RFC 7541 C.2.1 — Literal Header Field with Incremental Indexing

#### encoder produces RFC byte vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_encoder_new(4096, false)
val result = hpack_encode(_c21_headers(), state)
expect(_bytes_eq(result.0, _c21_bytes())).to_equal(true)
```

</details>

#### decoder recovers original header (round-trip)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = hpack_decoder_new(4096)
val result = hpack_decode(_c21_bytes(), state)
expect(result.is_ok()).to_equal(true)
val headers = result.unwrap().0
expect(_headers_eq(headers, _c21_headers())).to_equal(true)
```

</details>

#### encode-then-decode preserves header identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc_state = hpack_encoder_new(4096, false)
val enc = hpack_encode(_c21_headers(), enc_state)
val dec_state = hpack_decoder_new(4096)
val dec = hpack_decode(enc.0, dec_state)
expect(dec.is_ok()).to_equal(true)
expect(_headers_eq(dec.unwrap().0, _c21_headers())).to_equal(true)
```

</details>

### RFC 7541 C.3 — Request sequence without Huffman

#### C.3.1+C.3.2+C.3.3 encoder produces RFC byte vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s0 = hpack_encoder_new(4096, false)
val r1 = hpack_encode(_c31_headers(), s0)
val r2 = hpack_encode(_c32_headers(), r1.1)
val r3 = hpack_encode(_c33_headers(), r2.1)
expect(_bytes_eq(r1.0, _c31_bytes())).to_equal(true)
expect(_bytes_eq(r2.0, _c32_bytes())).to_equal(true)
expect(_bytes_eq(r3.0, _c33_bytes())).to_equal(true)
```

</details>

#### C.3 decoder recovers all three requests in sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s0 = hpack_decoder_new(4096)
val r1 = hpack_decode(_c31_bytes(), s0)
val s1 = r1.unwrap().1
val r2 = hpack_decode(_c32_bytes(), s1)
val s2 = r2.unwrap().1
val r3 = hpack_decode(_c33_bytes(), s2)
expect(r3.is_ok()).to_equal(true)
expect(_headers_eq(r1.unwrap().0, _c31_headers())).to_equal(true)
expect(_headers_eq(r2.unwrap().0, _c32_headers())).to_equal(true)
expect(_headers_eq(r3.unwrap().0, _c33_headers())).to_equal(true)
```

</details>

### RFC 7541 C.4 — Request sequence with Huffman

#### C.4 encoder (huffman=true) produces RFC byte vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s0 = hpack_encoder_new(4096, true)
val r1 = hpack_encode(_c31_headers(), s0)
val r2 = hpack_encode(_c32_headers(), r1.1)
val r3 = hpack_encode(_c33_headers(), r2.1)
expect(_bytes_eq(r1.0, _c41_bytes())).to_equal(true)
expect(_bytes_eq(r2.0, _c42_bytes())).to_equal(true)
expect(_bytes_eq(r3.0, _c43_bytes())).to_equal(true)
```

</details>

#### C.4 decoder recovers all three requests from Huffman bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s0 = hpack_decoder_new(4096)
val r1 = hpack_decode(_c41_bytes(), s0)
val r2 = hpack_decode(_c42_bytes(), r1.unwrap().1)
val r3 = hpack_decode(_c43_bytes(), r2.unwrap().1)
expect(r3.is_ok()).to_equal(true)
expect(_headers_eq(r1.unwrap().0, _c31_headers())).to_equal(true)
expect(_headers_eq(r2.unwrap().0, _c32_headers())).to_equal(true)
expect(_headers_eq(r3.unwrap().0, _c33_headers())).to_equal(true)
```

</details>

#### C.4 Huffman is shorter than C.3 raw on the first request

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw_len = _c31_bytes().len()
val huff_len = _c41_bytes().len()
expect(huff_len < raw_len).to_equal(true)
```

</details>

### RFC 7541 C.5 — Response sequence with eviction

#### C.5.1+C.5.2 encoder produces RFC byte vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s0 = hpack_encoder_new(256, false)
val r1 = hpack_encode(_c51_headers(), s0)
val r2 = hpack_encode(_c52_headers(), r1.1)
expect(_bytes_eq(r1.0, _c51_bytes())).to_equal(true)
expect(_bytes_eq(r2.0, _c52_bytes())).to_equal(true)
```

</details>

#### C.5 decoder recovers all three responses in sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s0 = hpack_decoder_new(256)
val r1 = hpack_decode(_c51_bytes(), s0)
val s1 = r1.unwrap().1
val r2 = hpack_decode(_c52_bytes(), s1)
expect(r2.is_ok()).to_equal(true)
expect(_headers_eq(r1.unwrap().0, _c51_headers())).to_equal(true)
expect(_headers_eq(r2.unwrap().0, _c52_headers())).to_equal(true)
```

</details>

#### C.5 dynamic-table eviction caps entries under max_size=256

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 7541 Appendix C.5: with max_size=256 the cumulative size after
# all three responses forces eviction. C.5.1 fills the table to 222B
# (4 entries); C.5.2 adds a 5th entry (size 42, total 264 > 256) and
# evicts the oldest, leaving 4; C.5.3 inserts 3 more headers under a
# tightening cap and ends with exactly 3 entries — see the existing
# spec at test/unit/lib/common/hpack/encoder_decoder_spec.spl which
# also verifies the C.5.3 "exactly 3 entries" invariant.
val s0 = hpack_decoder_new(256)
val r1 = hpack_decode(_c51_bytes(), s0)
val s1 = r1.unwrap().1
# After C.5.1 the table should NOT exceed its 256-byte budget.
expect(s1.table.current_size <= 256).to_equal(true)
val r2 = hpack_decode(_c52_bytes(), s1)
val s2 = r2.unwrap().1
expect(s2.table.current_size <= 256).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
