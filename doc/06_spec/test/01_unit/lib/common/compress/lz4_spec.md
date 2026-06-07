# LZ4 Block Compression Round-Trip Tests

> 1. check

<!-- sdn-diagram:id=lz4_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lz4_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lz4_spec -> std
lz4_spec -> compress
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lz4_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LZ4 Block Compression Round-Trip Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COMPRESS-LZ4 |
| Category | Compression |
| Status | Implemented |
| Source | `test/01_unit/lib/common/compress/lz4_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### LZ4 block compression

#### round-trip Hello World

1. check
2. check
3. check
4. check
5. check
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _make_hello_world_bytes()
val compressed = lz4_compress_block(data)
val result = lz4_decompress_block(compressed)
check(result.is_ok())
val decompressed = result.unwrap()
check(decompressed.len() == 13)
check(decompressed[0] == 0x48u8)
check(decompressed[1] == 0x65u8)
check(decompressed[4] == 0x6fu8)
check(decompressed[12] == 0x21u8)
```

</details>

#### round-trip repeated data compresses

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _make_repeated_bytes(0x41u8, 10)
val compressed = lz4_compress_block(data)
val result = lz4_decompress_block(compressed)
check(result.is_ok())
val decompressed = result.unwrap()
check(decompressed.len() == 10)
check(decompressed[0] == 0x41u8)
check(decompressed[9] == 0x41u8)
```

</details>

#### round-trip empty input

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty: [u8] = []
val compressed = lz4_compress_block(empty)
val result = lz4_decompress_block(compressed)
check(result.is_ok())
val decompressed = result.unwrap()
check(decompressed.len() == 0)
```

</details>

#### round-trip longer data 128 bytes

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _make_sequential_bytes(128)
val compressed = lz4_compress_block(data)
val result = lz4_decompress_block(compressed)
check(result.is_ok())
val decompressed = result.unwrap()
check(decompressed.len() == 128)
check(decompressed[0] == 0x00u8)
check(decompressed[127] == 0x7fu8)
```

</details>

#### repeated data compressed is smaller

1. check
2. check
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _make_repeated_bytes(0x42u8, 1000)
val compressed = lz4_compress_block_with_level(data, 6)
check(compressed.len() < 1000)
val result = lz4_decompress_block(compressed)
check(result.is_ok())
val decompressed = result.unwrap()
check(decompressed.len() == 1000)
check(decompressed[0] == 0x42u8)
check(decompressed[999] == 0x42u8)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
