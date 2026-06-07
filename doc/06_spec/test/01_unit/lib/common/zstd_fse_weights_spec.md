# Zstd Fse Weights Specification

> <details>

<!-- sdn-diagram:id=zstd_fse_weights_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=zstd_fse_weights_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

zstd_fse_weights_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=zstd_fse_weights_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Fse Weights Specification

## Scenarios

### zstd FSE-compressed Huffman-weight decode (RFC 8478 §4.2.1.1)

#### decodes a real host-zstd FSE Huffman tree byte-exact

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = zstd_parse_fse_huffman_weights(FX1, 0, FX1.len())
expect(res.is_err()).to_equal(false)
val (weights, bytes_used) = res.unwrap()
# FX1's compressed_size = 0x15 = 21, plus 1 header byte -> 22 consumed.
expect(bytes_used).to_equal(22)
# Partial weight stream produces 122 entries summing to 126 (= 2^7 - 2);
# Kraft completion appends last_weight = 2 for a total of 123 entries.
expect(weights.len()).to_equal(123)
expect(weights[122]).to_equal(2)
# Spot-check a few characteristic indices: ' '=32 -> weight 5 (frequent);
# '.'=46 -> weight 1 (rare); 'a'=97 -> weight 4; 'y'=121 -> weight 3.
expect(weights[32]).to_equal(5)
expect(weights[46]).to_equal(1)
expect(weights[97]).to_equal(4)
expect(weights[121]).to_equal(3)
```

</details>

#### decodes a fresh host-zstd FSE Huffman tree byte-exact

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = zstd_parse_fse_huffman_weights(FX_HOST_FRESH, 0, FX_HOST_FRESH.len())
expect(res.is_err()).to_equal(false)
val (weights, bytes_used) = res.unwrap()
# FX_HOST_FRESH's compressed_size = 0x19 = 25, plus 1 header byte.
expect(bytes_used).to_equal(26)
# 122 partial weights sum to 255; last_weight = 1 -> 123 total, sum 256 = 2^8.
expect(weights.len()).to_equal(123)
expect(weights[122]).to_equal(1)
```

</details>

#### rejects a truncated FSE Huffman-weight bitstream

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = zstd_parse_fse_huffman_weights(FX_TRUNCATED, 0, FX_TRUNCATED.len())
expect(res.is_err()).to_equal(true)
_expect_compression_error(res.unwrap_err(), "TruncatedInput", "compressed Huffman weights")
```

</details>

#### rejects an out-of-range accuracy_log

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = zstd_parse_fse_huffman_weights(FX_BAD_ACC_LOG, 0, FX_BAD_ACC_LOG.len())
expect(res.is_err()).to_equal(true)
# The low nibble asks for table_log=17; Huffman weight FSE caps this at 6.
_expect_compression_error(res.unwrap_err(), "CorruptStream", "caller maximum")
```

</details>

#### rejects a zero compressed-size header

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = zstd_parse_fse_huffman_weights(FX_ZERO_COMP, 0, FX_ZERO_COMP.len())
expect(res.is_err()).to_equal(true)
_expect_compression_error(res.unwrap_err(), "CorruptStream", "compressed Huffman weights size")
```

</details>

#### rejects empty input at the Huffman tree header

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val res = zstd_parse_fse_huffman_weights(empty, 0, 0)
expect(res.is_err()).to_equal(true)
_expect_compression_error(res.unwrap_err(), "TruncatedInput", "huffman tree header")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/zstd_fse_weights_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- zstd FSE-compressed Huffman-weight decode (RFC 8478 §4.2.1.1)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
