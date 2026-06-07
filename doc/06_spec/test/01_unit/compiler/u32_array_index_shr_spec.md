# U32 Array Index Shr Specification

> <details>

<!-- sdn-diagram:id=u32_array_index_shr_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=u32_array_index_shr_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

u32_array_index_shr_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=u32_array_index_shr_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# U32 Array Index Shr Specification

## Scenarios

### Indexed `[u32]` read narrows before `>>` (A2 / FR-DRIVER-0002b array variant)

#### AC-1a: arr[0] >> 3 with arr[0]=0x80000000 yields 0x10000000 (unsigned logical shift)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val got: u32 = u32_array_high_bit_shr3()
val expected: u32 = 0x10000000 as u32
expect(got).to_equal(expected)
```

</details>

#### AC-1b: arr[0] >> 3 with arr[0]=0xFFFFFFFF yields 0x1FFFFFFF (unsigned logical shift)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val got: u32 = u32_array_all_ones_shr3()
val expected: u32 = 0x1FFFFFFF as u32
expect(got).to_equal(expected)
```

</details>

#### AC-1c: SHA-recurrence shape `arr[a] + ((arr[b] >> 3) ^ arr[c])` yields unsigned-correct 0x210F0F0F

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Mirrors `w[t-16] + small_sigma0-like(w[t-15]) + ... ^ ...` from
# src/os/crypto/sha256.spl:220-280 at minimum scale.  Distinguishes
# signed-i64 lowering (wrong: 0x010F0F0F) from u32-narrowed (right).
val got: u32 = u32_sha_recurrence_shape()
val expected: u32 = 0x210F0F0F as u32
expect(got).to_equal(expected)
```

</details>

<details>
<summary>Advanced: AC-1d: for-loop `for w in arr: acc += w >> 3` matches direct indexed read</summary>

#### AC-1d: for-loop `for w in arr: acc += w >> 3` matches direct indexed read

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val got: u32 = u32_array_for_loop_shr3()
val expected: u32 = 0x10000000 as u32
expect(got).to_equal(expected)
```

</details>


</details>

#### AC-1e: signed [i32] arr[0] >> 3 still arithmetic-shifts (-1 >> 3 == -1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Guard against an over-eager fix that drops signedness for [i32] too.
# SIGNED narrow path must keep `signed: true` in UnitNarrow so the
# downstream `>>` dispatches to `sshr`.
expect(i32_array_minus_one_shr3()).to_equal(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/u32_array_index_shr_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Indexed `[u32]` read narrows before `>>` (A2 / FR-DRIVER-0002b array variant)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
