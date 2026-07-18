# Zstd Huf Specification

> <details>

<!-- sdn-diagram:id=zstd_huf_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=zstd_huf_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

zstd_huf_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=zstd_huf_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Huf Specification

## Scenarios

### zstd huffman helpers

#### completes weights and assigns canonical codes using zstd ordering

-  expect entry
-  expect entry
-  expect entry
-  expect entry
-  expect entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val complete_res = zstd_huf_complete_weights([4, 3, 2, 0, 1])
expect(complete_res.is_err()).to_equal(false)
val weights = complete_res.unwrap()
expect(weights.len()).to_equal(6)
expect(weights[5]).to_equal(1)

val symbols_res = zstd_huf_weights_to_symbols(weights)
expect(symbols_res.is_err()).to_equal(false)
val symbols = symbols_res.unwrap()
expect(symbols[0].bits).to_equal(1)
expect(symbols[1].bits).to_equal(2)
expect(symbols[2].bits).to_equal(3)
expect(symbols[3].bits).to_equal(0)
expect(symbols[4].bits).to_equal(4)
expect(symbols[5].bits).to_equal(4)

val entries_res = zstd_huf_build_canonical_entries(weights)
expect(entries_res.is_err()).to_equal(false)
val entries = entries_res.unwrap()
expect(entries.len()).to_equal(5)
_expect_entry(entries[0], 4, 1, 4, 0u32)
_expect_entry(entries[1], 5, 1, 4, 1u32)
_expect_entry(entries[2], 2, 2, 3, 1u32)
_expect_entry(entries[3], 1, 3, 2, 1u32)
_expect_entry(entries[4], 0, 4, 1, 1u32)
```

</details>

#### expands an lsb-indexed decode table for the backward bit reader

- ZstdHufCanonicalEntry
- ZstdHufCanonicalEntry
- ZstdHufCanonicalEntry
- ZstdHufCanonicalEntry
- ZstdHufCanonicalEntry
   - Expected: zstd_huf_reverse_bits(1u32, 3) equals `4u32`
   - Expected: table_res.is_err() is false
   - Expected: table.len() equals `16`
   - Expected: table[0].symbol equals `4`
   - Expected: table[0].bits equals `4`
   - Expected: table[8].symbol equals `5`
   - Expected: table[8].bits equals `4`
   - Expected: table[4].symbol equals `2`
   - Expected: table[12].symbol equals `2`
   - Expected: table[2].symbol equals `1`
   - Expected: table[6].symbol equals `1`
   - Expected: table[10].symbol equals `1`
   - Expected: table[14].symbol equals `1`
   - Expected: table[1].symbol equals `0`
   - Expected: table[15].symbol equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entries = [
    ZstdHufCanonicalEntry(symbol: 4, weight: 1, bits: 4, code: 0u32),
    ZstdHufCanonicalEntry(symbol: 5, weight: 1, bits: 4, code: 1u32),
    ZstdHufCanonicalEntry(symbol: 2, weight: 2, bits: 3, code: 1u32),
    ZstdHufCanonicalEntry(symbol: 1, weight: 3, bits: 2, code: 1u32),
    ZstdHufCanonicalEntry(symbol: 0, weight: 4, bits: 1, code: 1u32)
]
expect(zstd_huf_reverse_bits(1u32, 3)).to_equal(4u32)
val table_res = zstd_huf_expand_decode_table(entries, 4)
expect(table_res.is_err()).to_equal(false)
val table = table_res.unwrap()
expect(table.len()).to_equal(16)
expect(table[0].symbol).to_equal(4)
expect(table[0].bits).to_equal(4)
expect(table[8].symbol).to_equal(5)
expect(table[8].bits).to_equal(4)
expect(table[4].symbol).to_equal(2)
expect(table[12].symbol).to_equal(2)
expect(table[2].symbol).to_equal(1)
expect(table[6].symbol).to_equal(1)
expect(table[10].symbol).to_equal(1)
expect(table[14].symbol).to_equal(1)
expect(table[1].symbol).to_equal(0)
expect(table[15].symbol).to_equal(0)
```

</details>

#### rejects oversubscribed and incomplete weight sets

-  expect compression error
   - Expected: under.is_err() is true
-  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val over = zstd_huf_weights_to_symbols([2, 2, 2, 2, 2])
expect(over.is_err()).to_equal(true)
_expect_compression_error(over.unwrap_err(), "CorruptStream", "oversubscribed")

val under = zstd_huf_weights_to_symbols([2, 1])
expect(under.is_err()).to_equal(true)
_expect_compression_error(under.unwrap_err(), "CorruptStream", "incomplete")
```

</details>

#### encodes a two-symbol alphabet with a one-bit tree

-  expect entry
-  expect entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val literals: [u8] = [0x41u8, 0x42u8, 0x41u8, 0x42u8, 0x41u8, 0x41u8]
val encoded_res = zstd_huf_encode_literals(literals)
expect(encoded_res.is_err()).to_equal(false)
val (_bitstream, weights) = encoded_res.unwrap()
expect(weights[0x41].to_i64()).to_equal(1)
expect(weights[0x42].to_i64()).to_equal(1)
val entries_res = zstd_huf_build_canonical_entries(weights)
expect(entries_res.is_err()).to_equal(false)
val entries = entries_res.unwrap()
expect(entries.len()).to_equal(2)
_expect_entry(entries[0], 65, 1, 1, 0u32)
_expect_entry(entries[1], 66, 1, 1, 1u32)
```

</details>

#### encodes a one-symbol literal stream via a bounded synthetic partner

-  expect entry
-  expect entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val literals: [u8] = [
    0x5Au8, 0x5Au8, 0x5Au8, 0x5Au8,
    0x5Au8, 0x5Au8, 0x5Au8, 0x5Au8,
    0x5Au8, 0x5Au8, 0x5Au8, 0x5Au8
]
val encoded_res = zstd_huf_encode_literals(literals)
expect(encoded_res.is_err()).to_equal(false)
val (_bitstream, weights) = encoded_res.unwrap()
expect(weights[0x5A].to_i64()).to_equal(1)
expect(weights[0].to_i64()).to_equal(1)
val entries_res = zstd_huf_build_canonical_entries(weights)
expect(entries_res.is_err()).to_equal(false)
val entries = entries_res.unwrap()
expect(entries.len()).to_equal(2)
_expect_entry(entries[0], 0, 1, 1, 0u32)
_expect_entry(entries[1], 90, 1, 1, 1u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/zstd_huf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- zstd huffman helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
