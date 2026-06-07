# Snappy Block Compression Unit Tests

> 1. check

<!-- sdn-diagram:id=snappy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=snappy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

snappy_spec -> std
snappy_spec -> compress
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=snappy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Snappy Block Compression Unit Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COMPRESS-SNAPPY |
| Category | Compression |
| Status | Implemented |
| Source | `test/01_unit/lib/common/compress/snappy_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Snappy block compression

#### round-trip empty input

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty: [u8] = []
val compressed = snappy_compress(empty)
check(compressed.len() == 1)
check(compressed[0] == 0x00u8)
val decompressed = snappy_decompress(compressed)
check(decompressed.len() == 0)
```

</details>

#### round-trip Hello World

1. check
2. check
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = [0x48u8, 0x65u8, 0x6cu8, 0x6cu8, 0x6fu8, 0x2cu8, 0x20u8, 0x57u8, 0x6fu8, 0x72u8, 0x6cu8, 0x64u8, 0x21u8]
val compressed = snappy_compress(data)
val decompressed = snappy_decompress(compressed)
check(decompressed.len() == 13)
check(decompressed[0] == 0x48u8)
check(decompressed[1] == 0x65u8)
check(decompressed[4] == 0x6fu8)
check(decompressed[12] == 0x21u8)
```

</details>

#### known vector Hello literal

1. check
2. check
3. check
4. check
5. check
6. check
7. check
8. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var expected: [u8] = [0x05u8, 0x10u8, 0x48u8, 0x65u8, 0x6cu8, 0x6cu8, 0x6fu8]
var data: [u8] = [0x48u8, 0x65u8, 0x6cu8, 0x6cu8, 0x6fu8]
val compressed = snappy_compress(data)
check(compressed.len() == 7)
check(compressed[0] == 0x05u8)
check(compressed[1] == 0x10u8)
check(compressed[2] == 0x48u8)
check(compressed[3] == 0x65u8)
check(compressed[4] == 0x6cu8)
check(compressed[5] == 0x6cu8)
check(compressed[6] == 0x6fu8)
```

</details>

#### round-trip repeated data compresses well

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _make_repeated_bytes(0x41u8, 1000)
val compressed = snappy_compress(data)
check(compressed.len() < 100)
val decompressed = snappy_decompress(compressed)
check(decompressed.len() == 1000)
check(decompressed[0] == 0x41u8)
check(decompressed[999] == 0x41u8)
```

</details>

#### round-trip ABCABCABC has copy elements

1. check
2. check
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = [0x41u8, 0x42u8, 0x43u8, 0x41u8, 0x42u8, 0x43u8, 0x41u8, 0x42u8, 0x43u8]
val compressed = snappy_compress(data)
val decompressed = snappy_decompress(compressed)
check(decompressed.len() == 9)
check(decompressed[0] == 0x41u8)
check(decompressed[3] == 0x41u8)
check(decompressed[6] == 0x41u8)
check(decompressed[8] == 0x43u8)
```

</details>

#### decompress rejects truncated input

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bad: [u8] = [0x05u8, 0x10u8]
val result = try_snappy_decompress(bad)
check(result.is_err())
```

</details>

#### decompress rejects length mismatch

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bad: [u8] = [0x0Au8, 0x10u8, 0x48u8, 0x65u8, 0x6cu8, 0x6cu8, 0x6fu8]
val result = try_snappy_decompress(bad)
check(result.is_err())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
