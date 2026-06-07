# Zstd Fse Specification

> 1.  expect compression error

<!-- sdn-diagram:id=zstd_fse_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=zstd_fse_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

zstd_fse_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=zstd_fse_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Fse Specification

## Scenarios

### zstd fse helpers

#### validates table log bounds explicitly

1.  expect compression error
   - Expected: high.is_err() is true
2.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = zstd_fse_validate_table_log(5, 9)
expect(ok.is_err()).to_equal(false)

val low = zstd_fse_validate_table_log(4, 9)
expect(low.is_err()).to_equal(true)
_expect_compression_error(low.unwrap_err(), "CorruptStream", "below minimum")

val high = zstd_fse_validate_table_log(10, 9)
expect(high.is_err()).to_equal(true)
_expect_compression_error(high.unwrap_err(), "CorruptStream", "caller maximum")
```

</details>

#### parses normalized counts including zero repeats and less-than-one probabilities

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val simple = zstd_fse_parse_normalized_counts([0x10u8, 0x3Fu8], 0, 2, 9, 8)
expect(simple.is_err()).to_equal(false)
val simple_counts = simple.unwrap()
expect(simple_counts.table_log).to_equal(5)
expect(simple_counts.counts).to_equal([16, 16])
expect(simple_counts.bytes_used).to_equal(2)

val repeated = zstd_fse_parse_normalized_counts([0x10u8, 0xA3u8, 0x0Fu8], 0, 3, 9, 8)
expect(repeated.is_err()).to_equal(false)
val repeated_counts = repeated.unwrap()
expect(repeated_counts.counts).to_equal([16, 0, 0, 16])
expect(repeated_counts.max_symbol).to_equal(3)

val minus_one = zstd_fse_parse_normalized_counts([0x00u8, 0xE1u8, 0x03u8], 0, 3, 9, 8)
expect(minus_one.is_err()).to_equal(false)
expect(minus_one.unwrap().counts).to_equal([15, -1, 16])
```

</details>

#### rejects truncated or out-of-range normalized count descriptions

1.  expect compression error
   - Expected: too_many.is_err() is true
2.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val truncated = zstd_fse_parse_normalized_counts([0x00u8], 0, 1, 9, 8)
expect(truncated.is_err()).to_equal(true)
_expect_compression_error(truncated.unwrap_err(), "TruncatedInput", "normalized counts")

val too_many = zstd_fse_parse_normalized_counts([0x10u8, 0xA3u8, 0x0Fu8], 0, 3, 9, 2)
expect(too_many.is_err()).to_equal(true)
_expect_compression_error(too_many.unwrap_err(), "CorruptStream", "caller maximum")
```

</details>

#### builds decode tables from validated normalized counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_res = zstd_fse_build_decode_table(5, [16, 16])
expect(table_res.is_err()).to_equal(false)
val table = table_res.unwrap()
expect(table.entries.len()).to_equal(32)
expect(_count_symbol(table, 0)).to_equal(16)
expect(_count_symbol(table, 1)).to_equal(16)
var i = 0
while i < table.entries.len():
    expect(table.entries[i].bits).to_equal(1)
    expect(table.entries[i].baseline % 2).to_equal(0)
    i = i + 1

val mixed_res = zstd_fse_build_decode_table(5, [15, -1, 16])
expect(mixed_res.is_err()).to_equal(false)
val mixed = mixed_res.unwrap()
expect(_count_symbol(mixed, 1)).to_equal(1)
expect(mixed.entries[31].symbol).to_equal(1)
expect(mixed.entries[31].bits).to_equal(5)
expect(mixed.entries[31].baseline).to_equal(0)
```

</details>

#### provides bounded state access for later decode wiring

1.  expect compression error


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_res = zstd_fse_build_decode_table(5, [16, 16])
expect(table_res.is_err()).to_equal(false)
val table = table_res.unwrap()

val init = zstd_fse_init_state(7, table)
expect(init.is_err()).to_equal(false)
val entry = zstd_fse_get_entry(table, init.unwrap())
expect(entry.is_err()).to_equal(false)
expect(entry.unwrap().bits).to_equal(1)

val bad_state = zstd_fse_init_state(32, table)
expect(bad_state.is_err()).to_equal(true)
_expect_compression_error(bad_state.unwrap_err(), "CorruptStream", "initial state")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/zstd_fse_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- zstd fse helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
