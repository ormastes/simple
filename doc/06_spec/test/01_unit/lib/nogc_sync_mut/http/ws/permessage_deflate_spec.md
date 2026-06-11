# Permessage Deflate Specification

> <details>

<!-- sdn-diagram:id=permessage_deflate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=permessage_deflate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

permessage_deflate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=permessage_deflate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Permessage Deflate Specification

## Scenarios

### permessage-deflate RFC 7692

#### RSV1 bit constant is 0x40

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(WS_PMCE_RSV1_BIT).to_equal(0x40)
```

</details>

#### ws_pmce_rsv1_required returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ws_pmce_rsv1_required()).to_equal(true)
```

</details>

#### compress Hello matches RFC 7692 §8.3.1 known vector

1. var compressed result = ws compress message
2. var compressed = compressed result unwrap
3. var expected =  make rfc7692 hello compressed
   - Expected: compressed.len() equals `7`
   - Expected: compressed equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var compressed_result = ws_compress_message(_make_hello())
var compressed = compressed_result.unwrap()
var expected = _make_rfc7692_hello_compressed()
expect(compressed.len()).to_equal(7)
expect(compressed).to_equal(expected)
```

</details>

#### decompress RFC 7692 Hello vector recovers Hello

1. var compressed =  make rfc7692 hello compressed
2. var decompressed result = ws decompress message
3. var decompressed = decompressed result unwrap
4. var expected =  make hello
   - Expected: decompressed.len() equals `5`
   - Expected: decompressed equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var compressed = _make_rfc7692_hello_compressed()
var decompressed_result = ws_decompress_message(compressed)
var decompressed = decompressed_result.unwrap()
var expected = _make_hello()
expect(decompressed.len()).to_equal(5)
expect(decompressed).to_equal(expected)
```

</details>

#### round-trips empty payload

1. var compressed result = ws compress message
2. var compressed = compressed result unwrap
3. var decompressed result = ws decompress message
4. var decompressed = decompressed result unwrap
   - Expected: decompressed.len() equals `0`
   - Expected: decompressed equals `empty`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty: [u8] = []
var compressed_result = ws_compress_message(empty)
var compressed = compressed_result.unwrap()
var decompressed_result = ws_decompress_message(compressed)
var decompressed = decompressed_result.unwrap()
expect(decompressed.len()).to_equal(0)
expect(decompressed).to_equal(empty)
```

</details>

#### round-trips Hello World

1. var input =  make hello world
2. var compressed result = ws compress message
3. var compressed = compressed result unwrap
4. var decompressed result = ws decompress message
5. var decompressed = decompressed result unwrap
   - Expected: decompressed.len() equals `input.len()`
   - Expected: decompressed equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var input = _make_hello_world()
var compressed_result = ws_compress_message(input)
var compressed = compressed_result.unwrap()
var decompressed_result = ws_decompress_message(compressed)
var decompressed = decompressed_result.unwrap()
expect(decompressed.len()).to_equal(input.len())
expect(decompressed).to_equal(input)
```

</details>

#### round-trips 500 bytes of repeated pattern

1. var input =  make repeated
2. var compressed result = ws compress message
3. var compressed = compressed result unwrap
   - Expected: compressed.len() < input.len() is true
4. var decompressed result = ws decompress message
5. var decompressed = decompressed result unwrap
   - Expected: decompressed.len() equals `input.len()`
   - Expected: decompressed equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var input = _make_repeated(500)
var compressed_result = ws_compress_message(input)
var compressed = compressed_result.unwrap()
# Repeated data must compress
expect(compressed.len() < input.len()).to_equal(true)
var decompressed_result = ws_decompress_message(compressed)
var decompressed = decompressed_result.unwrap()
expect(decompressed.len()).to_equal(input.len())
expect(decompressed).to_equal(input)
```

</details>

#### compressed output does not end in 00 00 FF FF (tail was stripped)

1. var compressed result = ws compress message
2. var compressed = compressed result unwrap
3. var n = compressed len
4. var b0 = compressed[n - 4] to i64
5. var b1 = compressed[n - 3] to i64
6. var b2 = compressed[n - 2] to i64
7. var b3 = compressed[n - 1] to i64
   - Expected: ends_with_tail is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var compressed_result = ws_compress_message(_make_hello())
var compressed = compressed_result.unwrap()
var n = compressed.len()
# The 4-byte sync-flush tail must be absent
var ends_with_tail = false
if n >= 4:
    var b0 = compressed[n - 4].to_i64()
    var b1 = compressed[n - 3].to_i64()
    var b2 = compressed[n - 2].to_i64()
    var b3 = compressed[n - 1].to_i64()
    if b0 == 0 and b1 == 0 and b2 == 255 and b3 == 255:
        ends_with_tail = true
expect(ends_with_tail).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/http/ws/permessage_deflate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- permessage-deflate RFC 7692

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
