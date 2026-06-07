# Deflate Specification

> <details>

<!-- sdn-diagram:id=deflate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=deflate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

deflate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=deflate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Deflate Specification

## Scenarios

### DEFLATE RFC 1951 encoder/decoder

#### decompresses known fixed-Huffman stream for Hello

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = _make_known_deflate_hello()
val decompressed = deflate_decompress(compressed)
val expected = _make_hello_bytes()
expect(decompressed.len()).to_equal(5)
expect(decompressed).to_equal(expected)
```

</details>

#### round-trips empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty: [u8] = []
val compressed = deflate_compress(empty)
val decompressed = deflate_decompress(compressed)
expect(decompressed.len()).to_equal(0)
expect(decompressed).to_equal(empty)
```

</details>

#### round-trips Hello World

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _make_hello_world_bytes()
val compressed = deflate_compress(input)
val decompressed = deflate_decompress(compressed)
expect(decompressed.len()).to_equal(input.len())
expect(decompressed).to_equal(input)
```

</details>

#### round-trips 1000 bytes of repeated pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _make_repeated_pattern(1000)
val compressed = deflate_compress(input)
# Repeated data should compress significantly
expect(compressed.len() < input.len()).to_equal(true)
val decompressed = deflate_decompress(compressed)
expect(decompressed.len()).to_equal(input.len())
expect(decompressed).to_equal(input)
```

</details>

#### compressed output is smaller than input for repetitive data

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = _make_repeated_pattern(1000)
val compressed = deflate_compress(input)
expect(compressed.len() < 100).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compress/deflate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DEFLATE RFC 1951 encoder/decoder

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
