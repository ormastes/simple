# Zstd Fse Round Trip Specification

> <details>

<!-- sdn-diagram:id=zstd_fse_round_trip_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=zstd_fse_round_trip_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

zstd_fse_round_trip_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=zstd_fse_round_trip_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Fse Round Trip Specification

## Scenarios

### zstd fse encoder round-trip

#### round-trips a tiny three-symbol alphabet

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# table_size = 32 (table_log=5). counts sum to 32.
val counts = [12, 12, 8]
val input = [0, 1, 2, 1, 0, 2, 1, 0]
val out_res = _round_trip(5, counts, input)
expect(out_res.is_err()).to_equal(false)
expect(out_res.unwrap()).to_equal(input)
```

</details>

#### round-trips a small symbol stream with a less-than-one symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Symbol 2 has probability 1/32 (count == -1) so it occupies a
# high slot; symbols 0 and 1 share the body of the table.
# 15 + 16 + |-1| = 32 = table_size.
val counts = [15, 16, -1]
val input = [0, 1, 0, 1, 2, 0, 1, 0, 1]
val out_res = _round_trip(5, counts, input)
expect(out_res.is_err()).to_equal(false)
expect(out_res.unwrap()).to_equal(input)
```

</details>

#### round-trips a longer mixed sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val counts = [10, 10, 6, 6]
val input = [
    0, 1, 2, 3, 0, 1, 2, 3,
    0, 0, 1, 1, 2, 3, 0, 1,
    2, 3, 0, 1, 2, 3, 0, 1
]
val out_res = _round_trip(5, counts, input)
expect(out_res.is_err()).to_equal(false)
expect(out_res.unwrap()).to_equal(input)
```

</details>

#### round-trips at table_log = 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 64-slot table; mix of high and low probabilities.
# 20+14+10+8+6+4+1+1 = 64 (last two are |-1|=1 each).
val counts = [20, 14, 10, 8, 6, 4, -1, -1]
val input = [0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6]
val out_res = _round_trip(6, counts, input)
expect(out_res.is_err()).to_equal(false)
expect(out_res.unwrap()).to_equal(input)
```

</details>

#### round-trips a single-symbol-dominant stream

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# One dominant symbol with all the mass except a single low-prob.
val counts = [30, -1, -1]
val input = [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]
val out_res = _round_trip(5, counts, input)
expect(out_res.is_err()).to_equal(false)
expect(out_res.unwrap()).to_equal(input)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/zstd_fse_round_trip_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- zstd fse encoder round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
