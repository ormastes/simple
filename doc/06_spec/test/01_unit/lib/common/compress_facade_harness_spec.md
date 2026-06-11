# Compress Facade Harness Specification

> 1.  fixture empty

<!-- sdn-diagram:id=compress_facade_harness_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compress_facade_harness_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compress_facade_harness_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compress_facade_harness_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compress Facade Harness Specification

## Scenarios

### common compression facade harness

#### round-trips deterministic framed fixtures across every public codec

1.  fixture empty
2.  fixture short
3.  fixture mixed
4.  fixture repetitive
5.  fixture incompressible
6.  fixture overlap heavy
7.  assert auto round trip
8.  assert auto round trip
9.  assert auto round trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payloads = [
    _fixture_empty(),
    _fixture_short(),
    _fixture_mixed(),
    _fixture_repetitive(256),
    _fixture_incompressible(1024),
    _fixture_overlap_heavy(4096)
]
for payload in payloads:
    _assert_auto_round_trip(CompressionCodec.lz4, payload)
    _assert_auto_round_trip(CompressionCodec.zstd, payload)
    _assert_auto_round_trip(CompressionCodec.lzma2, payload)
```

</details>

#### requires an explicit lz4 block hint for deterministic raw-block fixtures

1.  assert lz4 block round trip
2.  assert lz4 block round trip
3.  assert lz4 block round trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_assert_lz4_block_round_trip(_fixture_short())
_assert_lz4_block_round_trip(_fixture_repetitive(128))
_assert_lz4_block_round_trip(_fixture_overlap_heavy(2048))
```

</details>

#### keeps the public facade byte-identical with forced scalar avx2 and neon tiers

1.  assert forced tier parity
2.  assert forced tier parity
3.  assert forced tier parity


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _fixture_overlap_heavy(8192) + _fixture_incompressible(1024)
_assert_forced_tier_parity(CompressionCodec.lz4, payload)
_assert_forced_tier_parity(CompressionCodec.zstd, payload)
_assert_forced_tier_parity(CompressionCodec.lzma2, payload)
```

</details>

#### returns typed invalid-header and truncation failures through the public facade

1.  expect error kind
2.  expect error kind
3.  expect error kind
4.  expect error kind
5.  expect error kind
6.  expect error kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _fixture_repetitive(512)

val lz4 = compress_bytes(payload, default_compression_options(CompressionCodec.lz4))
val zstd = compress_bytes(payload, default_compression_options(CompressionCodec.zstd))
val xz = compress_bytes(payload, default_compression_options(CompressionCodec.lzma2))

var bad_lz4 = lz4
bad_lz4[0] = bad_lz4[0] ^ 0x01u8
_expect_error_kind(decompress_bytes(bad_lz4, nil), "InvalidHeader")

var bad_zstd = zstd
bad_zstd[0] = bad_zstd[0] ^ 0x01u8
_expect_error_kind(decompress_bytes(bad_zstd, nil), "InvalidHeader")

var bad_xz = xz
bad_xz[0] = bad_xz[0] ^ 0x01u8
_expect_error_kind(decompress_bytes(bad_xz, nil), "InvalidHeader")

_expect_error_kind(decompress_bytes(lz4.slice(0, lz4.len() - 1), nil), "TruncatedInput")
_expect_error_kind(decompress_bytes(zstd.slice(0, zstd.len() - 1), nil), "TruncatedInput")
_expect_error_kind(decompress_bytes(xz.slice(0, xz.len() - 1), nil), "TruncatedInput")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compress_facade_harness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- common compression facade harness

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
