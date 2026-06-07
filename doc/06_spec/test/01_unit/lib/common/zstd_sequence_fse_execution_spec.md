# Zstd Sequence Fse Execution Specification

> 1. bits =  append lsb bits

<!-- sdn-diagram:id=zstd_sequence_fse_execution_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=zstd_sequence_fse_execution_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

zstd_sequence_fse_execution_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=zstd_sequence_fse_execution_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Sequence Fse Execution Specification

## Scenarios

### zstd fse/predefined sequence execution

#### encodes decoder-read bitstreams for mixed fixtures explicitly

1. bits =  append lsb bits
2. bits =  append lsb bits
3. bits =  append lsb bits
4. bits =  append lsb bits
5. bits =  append lsb bits
   - Expected: _zstd_reverse_bitstream_from_reads(bits) equals `[0x48u8, 0x20u8, 0x02u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bits: [i64] = []
bits = _append_lsb_bits(bits, 0, 6)
bits = _append_lsb_bits(bits, 1, 5)
bits = _append_lsb_bits(bits, 2, 4)
bits = _append_lsb_bits(bits, 1, 1)
bits = _append_lsb_bits(bits, 0, 1)
expect(_zstd_reverse_bitstream_from_reads(bits)).to_equal([0x48u8, 0x20u8, 0x02u8])
```

</details>

#### reverses longer decoder-read bitstreams with a nontrivial tail

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bits = [
    1, 0, 1, 0, 1,
    1, 0, 0, 1, 1, 1, 0, 0,
    1, 1, 0, 1, 1, 0, 1, 1,
    0, 1, 1, 0, 0, 1, 0, 1
]
expect(_zstd_reverse_bitstream_from_reads(bits)).to_equal([0xA6u8, 0xDBu8, 0x39u8, 0x35u8])
```

</details>

#### executes a sequence using a predefined ll table and rle offset/ml tables

1.  raw block
2.  compressed block
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[0x61u8, 0x62u8, 0x63u8, 0x61u8, 0x62u8, 0x63u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bits = [
    0, 0, 0, 0, 0, 0,
    0, 1
]
val sequence_stream = _zstd_reverse_bitstream(bits)
val payload = [
    0x00u8,
    0x01u8,
    0x14u8,
    0x02u8, 0x00u8
] + sequence_stream
val frame = _zstd_frame(6,
    _raw_block(false, [0x61u8, 0x62u8, 0x63u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x62u8, 0x63u8, 0x61u8, 0x62u8, 0x63u8])
```

</details>

#### fails closed on offset code 31 with an invalid match offset instead of unsupported-feature gating

1.  raw block
2.  compressed block
   - Expected: decoded.is_err() is true
3.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bits = [
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0
]
val sequence_stream = _zstd_reverse_bitstream_from_reads(bits)
val payload = [
    0x00u8,
    0x01u8,
    0x14u8,
    0x1Fu8, 0x00u8
] + sequence_stream
val frame = _zstd_frame(4,
    _raw_block(false, [0x61u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "invalid match offset")
```

</details>

#### executes a sequence using an fse-compressed ll table with a prior raw block

1.  raw block
2.  compressed block
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[0x61u8, 0x62u8, 0x63u8, 0x61u8, 0x62u8, 0x63u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bits = [
    0, 0, 0, 0, 0,
    0, 1
]
val sequence_stream = _zstd_reverse_bitstream(bits)
val payload = [
    0x00u8,
    0x01u8,
    0x94u8,
    0x10u8, 0x3Fu8,
    0x02u8, 0x00u8
] + sequence_stream
val frame = _zstd_frame(6,
    _raw_block(false, [0x61u8, 0x62u8, 0x63u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x62u8, 0x63u8, 0x61u8, 0x62u8, 0x63u8])
```

</details>

#### executes two sequences using a predefined ll table with state advancement

1.  raw block
2.  compressed block
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bits = [
    0, 0, 0, 0, 0, 0,
    0, 0,
    0, 0, 0, 0,
    0, 0
]
val sequence_stream = _zstd_reverse_bitstream_from_reads(bits)
val payload = [
    0x00u8,
    0x02u8,
    0x14u8,
    0x02u8, 0x00u8
] + sequence_stream
val frame = _zstd_frame(7,
    _raw_block(false, [0x61u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8])
```

</details>

#### executes two sequences using an fse-compressed ll table with state advancement

1.  raw block
2.  compressed block
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bits = [
    0, 0, 0, 0, 0,
    0, 0,
    0,
    0, 0
]
val sequence_stream = _zstd_reverse_bitstream_from_reads(bits)
val payload = [
    0x00u8,
    0x02u8,
    0x94u8,
    0x10u8, 0x3Fu8,
    0x02u8, 0x00u8
] + sequence_stream
val frame = _zstd_frame(7,
    _raw_block(false, [0x61u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8])
```

</details>

#### executes two sequences using a predefined offset table with state advancement

1.  raw block
2.  compressed block
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bits = [
    0, 1, 1, 1, 0,
    0, 0,
    0, 1, 1, 1, 0,
    0, 0
]
val sequence_stream = _zstd_reverse_bitstream_from_reads(bits)
val payload = [
    0x00u8,
    0x02u8,
    0x44u8,
    0x00u8, 0x00u8
] + sequence_stream
val frame = _zstd_frame(7,
    _raw_block(false, [0x61u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8])
```

</details>

#### executes a sequence using a predefined match-length table

1.  raw block
2.  compressed block
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bits = [
    1, 0, 0, 0, 0, 0,
    0, 0
]
val sequence_stream = _zstd_reverse_bitstream_from_reads(bits)
val payload = [
    0x00u8,
    0x01u8,
    0x50u8,
    0x00u8, 0x02u8
] + sequence_stream
val frame = _zstd_frame(5,
    _raw_block(false, [0x61u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8])
```

</details>

#### executes a sequence with predefined offset and match-length tables together

1.  raw block
2.  compressed block
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bits = [
    0, 0, 0, 0, 0,
    1, 0, 0, 0, 0, 0
]
val sequence_stream = _zstd_reverse_bitstream_from_reads(bits)
val payload = [
    0x00u8,
    0x01u8,
    0x40u8,
    0x00u8
] + sequence_stream
val frame = _zstd_frame(8,
    _raw_block(false, [0x61u8, 0x61u8, 0x61u8, 0x61u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8])
```

</details>

#### executes two sequences with predefined offset and match-length state advancement

1.  raw block
2.  compressed block
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bits = [
    0, 0, 1, 1, 1, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 0, 0,
    0, 1, 1, 1, 0, 1, 0, 0
]
val sequence_stream = _zstd_reverse_bitstream(bits)
val payload = [
    0x00u8,
    0x02u8,
    0x40u8,
    0x00u8
] + sequence_stream
val frame = _zstd_frame(9,
    _raw_block(false, [0x61u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8])
```

</details>

#### executes two mixed sequences with predefined ll, compressed of, and rle ml tables

1. bits =  append lsb bits
2. bits =  append lsb bits
3. bits =  append lsb bits
4. bits =  append lsb bits
5. bits =  append lsb bits
6.  raw block
7.  compressed block
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bits: [i64] = []
bits = _append_lsb_bits(bits, 0, 6)
bits = _append_lsb_bits(bits, 1, 5)
bits = _append_lsb_bits(bits, 2, 4)
bits = _append_lsb_bits(bits, 1, 1)
bits = _append_lsb_bits(bits, 1, 1)
val sequence_stream = _zstd_reverse_bitstream_from_reads(bits)
val payload = [
    0x08u8,
    0x7Au8,
    0x02u8,
    0x24u8,
    0x10u8, 0x3Fu8,
    0x00u8
] + sequence_stream
val frame = _zstd_frame(11,
    _raw_block(false, [0x61u8, 0x62u8, 0x63u8, 0x64u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([
    0x61u8, 0x62u8, 0x63u8, 0x64u8,
    0x61u8, 0x62u8, 0x63u8,
    0x7Au8, 0x61u8, 0x62u8, 0x63u8
])
```

</details>

#### executes two mixed sequences with rle ll, compressed of, and predefined ml tables

1. bits =  append lsb bits
2. bits =  append lsb bits
3. bits =  append lsb bits
4. bits =  append lsb bits
5. bits =  append lsb bits
6.  raw block
7.  compressed block
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bits: [i64] = []
bits = _append_lsb_bits(bits, 1, 5)
bits = _append_lsb_bits(bits, 0, 6)
bits = _append_lsb_bits(bits, 1, 6)
bits = _append_lsb_bits(bits, 1, 1)
bits = _append_lsb_bits(bits, 0, 1)
val sequence_stream = _zstd_reverse_bitstream_from_reads(bits)
val payload = [
    0x00u8,
    0x02u8,
    0x60u8,
    0x00u8,
    0x10u8, 0x3Fu8
] + sequence_stream
val frame = _zstd_frame(12,
    _raw_block(false, [0x61u8, 0x62u8, 0x63u8, 0x64u8, 0x65u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([
    0x61u8, 0x62u8, 0x63u8, 0x64u8, 0x65u8,
    0x62u8, 0x63u8, 0x64u8,
    0x61u8, 0x62u8, 0x63u8, 0x64u8
])
```

</details>

#### executes three mixed sequences with repeat-offset resolution after history changes

1. bits =  append lsb bits
2. bits =  append lsb bits
3. bits =  append lsb bits
4. bits =  append lsb bits
5. bits =  append lsb bits
6. bits =  append lsb bits
7. bits =  append lsb bits
8. bits =  append lsb bits
9. bits =  append lsb bits
10. bits =  append lsb bits
11. bits =  append lsb bits
12.  raw block
13.  compressed block
   - Expected: decoded.is_err() is false
   - Expected: decoded.unwrap() equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bits: [i64] = []
bits = _append_lsb_bits(bits, 0, 5)
bits = _append_lsb_bits(bits, 5, 5)
bits = _append_lsb_bits(bits, 0, 6)
bits = _append_lsb_bits(bits, 0, 3)
bits = _append_lsb_bits(bits, 1, 1)
bits = _append_lsb_bits(bits, 0, 6)
bits = _append_lsb_bits(bits, 23, 5)
bits = _append_lsb_bits(bits, 0, 1)
bits = _append_lsb_bits(bits, 1, 1)
bits = _append_lsb_bits(bits, 0, 6)
bits = _append_lsb_bits(bits, 0, 5)
val sequence_stream = _zstd_reverse_bitstream_from_reads(bits)
val payload = [
    0x08u8,
    0x7Au8,
    0x03u8,
    0x80u8,
    0x10u8, 0x3Fu8
] + sequence_stream
val frame = _zstd_frame(15,
    _raw_block(false, [0x61u8, 0x62u8, 0x63u8, 0x64u8, 0x65u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap()).to_equal([
    0x61u8, 0x62u8, 0x63u8, 0x64u8, 0x65u8,
    0x61u8, 0x62u8, 0x63u8,
    0x65u8, 0x61u8, 0x62u8,
    0x7Au8, 0x65u8, 0x61u8, 0x62u8
])
```

</details>

#### fails closed when a predefined/fse sequence bitstream is truncated

1.  raw block
2.  compressed block
   - Expected: decoded.is_err() is true
3.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = [
    0x00u8,
    0x01u8,
    0x14u8,
    0x02u8, 0x00u8,
    0x00u8
]
val frame = _zstd_frame(6,
    _raw_block(false, [0x61u8, 0x62u8, 0x63u8]) +
    _compressed_block(true, payload)
)
val decoded = decompress_bytes(frame, Some(CompressionCodec.zstd))
expect(decoded.is_err()).to_equal(true)
_expect_compression_error(decoded.unwrap_err(), "CorruptStream", "end mark")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/zstd_sequence_fse_execution_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- zstd fse/predefined sequence execution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
