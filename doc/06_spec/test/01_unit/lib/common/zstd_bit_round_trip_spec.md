# Zstd Bit Round Trip Specification

> <details>

<!-- sdn-diagram:id=zstd_bit_round_trip_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=zstd_bit_round_trip_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

zstd_bit_round_trip_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=zstd_bit_round_trip_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Bit Round Trip Specification

## Scenarios

### zstd bit writer/reader round-trip

#### msb writer + msb backward reader recover the same value

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w0 = zstd_bit_writer_new()
val w1_res = zstd_bit_writer_append_msb(w0, 4u64, 3)
expect(w1_res.is_err()).to_equal(false)
val w1 = w1_res.unwrap()
val bytes_res = zstd_bit_writer_finish(w1)
expect(bytes_res.is_err()).to_equal(false)
val bytes = bytes_res.unwrap()
val r0_res = zstd_msb_bits_init(bytes, 0, bytes.len())
expect(r0_res.is_err()).to_equal(false)
val r0 = r0_res.unwrap()
val v_res = zstd_msb_bits_read(r0, 3)
expect(v_res.is_err()).to_equal(false)
val (v, _r, _p) = v_res.unwrap()
expect(v).to_equal(4)
```

</details>

#### lsb writer + msb backward reader recover the same value

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w0 = zstd_bit_writer_new()
val w1_res = zstd_bit_writer_append_lsb(w0, 4u64, 3)
val w1 = w1_res.unwrap()
val bytes = zstd_bit_writer_finish(w1).unwrap()
val r0 = zstd_msb_bits_init(bytes, 0, bytes.len()).unwrap()
val (v, _r, _p) = zstd_msb_bits_read(r0, 3).unwrap()
expect(v).to_equal(4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/zstd_bit_round_trip_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- zstd bit writer/reader round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
