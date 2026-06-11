# Gzip Specification

> 1. input push

<!-- sdn-diagram:id=gzip_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gzip_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gzip_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gzip_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gzip Specification

## Scenarios

### gzip RFC 1952

#### round-trips Hello, World!

1. input push
2. input push
3. input push
4. input push
5. input push
6. input push
7. input push
8. input push
9. input push
10. input push
11. input push
12. input push
13. input push
   - Expected: decompressed equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var input: [u8] = []
# "Hello, World!" = [72, 101, 108, 108, 111, 44, 32, 87, 111, 114, 108, 100, 33]
var b0: u8 = 72u8
input.push(b0)
var b1: u8 = 101u8
input.push(b1)
var b2: u8 = 108u8
input.push(b2)
var b3: u8 = 108u8
input.push(b3)
var b4: u8 = 111u8
input.push(b4)
var b5: u8 = 44u8
input.push(b5)
var b6: u8 = 32u8
input.push(b6)
var b7: u8 = 87u8
input.push(b7)
var b8: u8 = 111u8
input.push(b8)
var b9: u8 = 114u8
input.push(b9)
var b10: u8 = 108u8
input.push(b10)
var b11: u8 = 100u8
input.push(b11)
var b12: u8 = 33u8
input.push(b12)

val compressed = gzip_compress(input)
val decompressed = gzip_decompress(compressed)
expect(decompressed).to_equal(input)
```

</details>

#### round-trips empty data

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty: [u8] = []
val compressed = gzip_compress(empty)
val decompressed = gzip_decompress(compressed)
expect(decompressed).to_equal(empty)
```

</details>

#### decompresses known Python-generated gzip stream

1. stream push
2. stream push
3. stream push
4. stream push
5. stream push
6. stream push
7. stream push
8. stream push
9. stream push
10. stream push
11. stream push
12. stream push
13. stream push
14. stream push
15. stream push
16. stream push
17. stream push
18. stream push
19. stream push
20. stream push
21. stream push
22. stream push
23. stream push
24. stream push
25. expected push
26. expected push
27. expected push
28. expected push
   - Expected: decompressed equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 73 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# From Python: gzip.compress(b"test") produces this exact stream
# Header: 1f 8b 08 00 00 00 00 00 00 03
# DEFLATE (fixed Huffman): 2b 49 2d 2e 01 00
# CRC-32: 0c 7e 7f d8  (LE of 0xD87F7E0C)
# ISIZE: 04 00 00 00
var stream: [u8] = []
# Header (10 bytes)
var h0: u8 = 0x1Fu8
stream.push(h0)
var h1: u8 = 0x8Bu8
stream.push(h1)
var h2: u8 = 0x08u8
stream.push(h2)
var h3: u8 = 0x00u8
stream.push(h3)
var h4: u8 = 0x00u8
stream.push(h4)
var h5: u8 = 0x00u8
stream.push(h5)
var h6: u8 = 0x00u8
stream.push(h6)
var h7: u8 = 0x00u8
stream.push(h7)
var h8: u8 = 0x00u8
stream.push(h8)
var h9: u8 = 0x03u8
stream.push(h9)
# DEFLATE fixed Huffman (6 bytes)
var d0: u8 = 0x2Bu8
stream.push(d0)
var d1: u8 = 0x49u8
stream.push(d1)
var d2: u8 = 0x2Du8
stream.push(d2)
var d3: u8 = 0x2Eu8
stream.push(d3)
var d4: u8 = 0x01u8
stream.push(d4)
var d5: u8 = 0x00u8
stream.push(d5)
# CRC-32 (LE of 0xD87F7E0C)
var c0: u8 = 0x0Cu8
stream.push(c0)
var c1: u8 = 0x7Eu8
stream.push(c1)
var c2: u8 = 0x7Fu8
stream.push(c2)
var c3: u8 = 0xD8u8
stream.push(c3)
# ISIZE = 4
var s0: u8 = 0x04u8
stream.push(s0)
var s1: u8 = 0x00u8
stream.push(s1)
var s2: u8 = 0x00u8
stream.push(s2)
var s3: u8 = 0x00u8
stream.push(s3)

val decompressed = gzip_decompress(stream)

# Expected: "test" = [116, 101, 115, 116]
var expected: [u8] = []
var e0: u8 = 116u8
expected.push(e0)
var e1: u8 = 101u8
expected.push(e1)
var e2: u8 = 115u8
expected.push(e2)
var e3: u8 = 116u8
expected.push(e3)

expect(decompressed).to_equal(expected)
```

</details>

#### computes correct CRC-32 for test

1. input push
2. input push
3. input push
4. input push
   - Expected: crc equals `0xD87F7E0Cu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# crc32("test") = 0xD87F7E0C
var input: [u8] = []
var t0: u8 = 116u8
input.push(t0)
var t1: u8 = 101u8
input.push(t1)
var t2: u8 = 115u8
input.push(t2)
var t3: u8 = 116u8
input.push(t3)

val crc = gzip_crc32(input)
expect(crc).to_equal(0xD87F7E0Cu32)
```

</details>

#### validates gzip header magic bytes

1. bad data push
2. bad data push
3. bad data push
4. bad data push
5. bad data push
6. bad data push
7. bad data push
8. bad data push
9. bad data push
10. bad data push
11. bad data push
12. bad data push
13. bad data push
14. bad data push
15. bad data push
16. bad data push
17. bad data push
18. bad data push
19. bad data push
20. bad data push
21. bad data push
22. bad data push
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Invalid magic should return empty
var bad_data: [u8] = []
var x0: u8 = 0x00u8
bad_data.push(x0)
var x1: u8 = 0x00u8
bad_data.push(x1)
var x2: u8 = 0x08u8
bad_data.push(x2)
var x3: u8 = 0x00u8
bad_data.push(x3)
var x4: u8 = 0x00u8
bad_data.push(x4)
var x5: u8 = 0x00u8
bad_data.push(x5)
var x6: u8 = 0x00u8
bad_data.push(x6)
var x7: u8 = 0x00u8
bad_data.push(x7)
var x8: u8 = 0x00u8
bad_data.push(x8)
var x9: u8 = 0xFFu8
bad_data.push(x9)
var x10: u8 = 0x01u8
bad_data.push(x10)
var x11: u8 = 0x00u8
bad_data.push(x11)
var x12: u8 = 0x00u8
bad_data.push(x12)
var x13: u8 = 0xFFu8
bad_data.push(x13)
var x14: u8 = 0xFFu8
bad_data.push(x14)
var x15: u8 = 0x00u8
bad_data.push(x15)
var x16: u8 = 0x00u8
bad_data.push(x16)
var x17: u8 = 0x00u8
bad_data.push(x17)
var x18: u8 = 0x00u8
bad_data.push(x18)
var x19: u8 = 0x00u8
bad_data.push(x19)
var x20: u8 = 0x00u8
bad_data.push(x20)
var x21: u8 = 0x00u8
bad_data.push(x21)

val result = gzip_decompress(bad_data)
expect(result.len()).to_equal(0)
```

</details>

#### detects CRC-32 mismatch

1. input push
2. input push
3. input push
4. var compressed = gzip compress
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Compress valid data, then corrupt CRC byte
var input: [u8] = []
var a0: u8 = 65u8
input.push(a0)
var a1: u8 = 66u8
input.push(a1)
var a2: u8 = 67u8
input.push(a2)

var compressed = gzip_compress(input)
# Corrupt CRC (last 8 bytes area, specifically the CRC)
val crc_offset: i64 = compressed.len() - 8
compressed[crc_offset] = compressed[crc_offset] ^ 0x01u8

val result = gzip_decompress(compressed)
expect(result.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compress/gzip_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gzip RFC 1952

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
