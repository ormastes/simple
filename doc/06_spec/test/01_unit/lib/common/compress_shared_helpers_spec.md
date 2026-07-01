# Compress Shared Helpers Specification

> <details>

<!-- sdn-diagram:id=compress_shared_helpers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compress_shared_helpers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compress_shared_helpers_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compress_shared_helpers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compress Shared Helpers Specification

## Scenarios

### compression shared helper kernels

#### decodes repeated match extension bytes until a terminating lane

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decoded = decode_match_extension_length(15, [255u8, 255u8, 7u8], 0, "lz4 match extension")
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap().length).to_equal(15 + 255 + 255 + 7)
expect(decoded.unwrap().next_pos).to_equal(3)
```

</details>

#### fails closed when match extension bytes are truncated

-  expect truncated


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decoded = decode_match_extension_length(15, [255u8], 0, "lz4 match extension")
expect(decoded.is_err()).to_equal(true)
_expect_truncated(decoded.unwrap_err(), "match extension")
```

</details>

#### copies checked literal ranges and advances the cursor

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val copied = append_literal_copy([0x00u8], _fixture_bytes(), 3, 6, "lz4 literal body")
expect(copied.is_err()).to_equal(false)
expect(copied.unwrap().out).to_equal([0x00u8, 0x61u8, 0x62u8, 0x63u8, 0x61u8, 0x62u8, 0x63u8])
expect(copied.unwrap().next_pos).to_equal(9)
```

</details>

#### fails closed when literal copy would read past the input

-  expect truncated


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val copied = append_literal_copy([], _fixture_bytes(), 22, 4, "lz4 literal body")
expect(copied.is_err()).to_equal(true)
_expect_truncated(copied.unwrap_err(), "literal body")
```

</details>

#### keeps overlap-safe match copy parity across explicit scalar avx2 and neon entrypoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = "ABCD".bytes()
val scalar = append_self_overlap_copy_scalar(base, 4, 8)
val avx2 = append_self_overlap_copy_avx2(base, 4, 8)
val neon = append_self_overlap_copy_neon(base, 4, 8)
val forced_scalar = append_self_overlap_copy_for_tier(base, 4, 8, CompressionSimdTier.scalar)
val forced_avx2 = append_self_overlap_copy_for_tier(base, 4, 8, CompressionSimdTier.avx2)
val forced_neon = append_self_overlap_copy_for_tier(base, 4, 8, CompressionSimdTier.neon)
expect(scalar.is_err()).to_equal(false)
expect(avx2.is_err()).to_equal(false)
expect(neon.is_err()).to_equal(false)
expect(forced_scalar.unwrap()).to_equal(scalar.unwrap())
expect(forced_avx2.unwrap()).to_equal(scalar.unwrap())
expect(forced_neon.unwrap()).to_equal(scalar.unwrap())
expect(append_self_overlap_copy(base, 4, 8).unwrap()).to_equal(scalar.unwrap())
expect(scalar.unwrap()).to_equal("ABCDABCDABCD".bytes())
```

</details>

#### matches crc32 vectors across the forced-tier helper entrypoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = _fixture_bytes()
val scalar = crc32_bytes_scalar(bytes)
expect(scalar).to_equal(crc32_bytes(bytes))
expect(crc32_bytes_avx2(bytes)).to_equal(scalar)
expect(crc32_bytes_neon(bytes)).to_equal(scalar)
expect(crc32_bytes_scalar("123456789".bytes())).to_equal(0xCBF43926u32)
```

</details>

#### matches xxh32 vectors across the forced-tier helper entrypoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = _fixture_bytes()
val seed = 0x9747B28Cu32
val scalar = xxhash32_bytes_scalar(bytes, seed)
expect(scalar).to_equal(xxhash32_bytes(bytes, seed))
expect(xxhash32_bytes_avx2(bytes, seed)).to_equal(scalar)
expect(xxhash32_bytes_neon(bytes, seed)).to_equal(scalar)
expect(xxhash32_bytes_scalar("123456789".bytes(), 0u32)).to_equal(0x937BAD67u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compress_shared_helpers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- compression shared helper kernels

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
