# Probe Wide Int Specification

> <details>

<!-- sdn-diagram:id=_probe_wide_int_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=_probe_wide_int_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

_probe_wide_int_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=_probe_wide_int_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Probe Wide Int Specification

## Scenarios

### u64 shift workaround

#### 0xffffffffffffffff >> 32 (arithmetic)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: u64 = 0xffffffffffffffff
val r: u64 = b >> 32
# If logical shift: r = 0xffffffff
# If arithmetic: r = 0xffffffffffffffff (i64 -1 sign-extended)
# The test result shows arithmetic
expect(r).to_equal(0xffffffffffffffff)
```

</details>

#### (b >> 32) & MASK32 workaround

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: u64 = 0xffffffffffffffff
val r: u64 = (b >> 32) & MASK32_T
expect(r).to_equal(0xffffffff)
```

</details>

#### small value: 0x12345678 >> 16 still works

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: u64 = 0x12345678
val r: u64 = b >> 16
expect(r).to_equal(0x1234)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/math/field/_probe_wide_int_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- u64 shift workaround

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
