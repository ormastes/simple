# Lshr Debug Specification

> <details>

<!-- sdn-diagram:id=lshr_debug_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lshr_debug_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lshr_debug_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lshr_debug_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lshr Debug Specification

## Scenarios

### lshr64 test

#### positive value shifts logically

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0x6f = 111, shift right 0 = 111
expect(_lshr64(111, 0)).to_equal(111)
```

</details>

#### negative value: -1 >> 1 should be max_i64 (0x7fffffffffffffff)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = _lshr64(-1, 1)
# Arithmetic shift: -1 >> 1 = -1 (sign extend)
# Logical shift: 0xFFFFFFFFFFFFFFFF >> 1 = 0x7FFFFFFFFFFFFFFF
expect(r).to_equal(9223372036854775807)
```

</details>

#### negative value >> 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# -1 (0xFFFFFFFFFFFF...) >> 8 should be 0x00FFFFFFFFFFFFFF
val r = _lshr64(-1, 8)
expect(r).to_equal(72057594037927935)
```

</details>

#### mask with -1 is no-op

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = -1
val r = x & -1
# In Python bignum, -1 & -1 = -1, same as i64 -1
expect(r).to_equal(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/lshr_debug_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- lshr64 test

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
