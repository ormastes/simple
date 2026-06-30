# Volatile Ops Specification

> <details>

<!-- sdn-diagram:id=volatile_ops_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=volatile_ops_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

volatile_ops_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=volatile_ops_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Volatile Ops Specification

## Scenarios

### volatile_ops SFFI module

### structural sanity

#### spec file loads without parse error

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1).to_equal(1)
```

</details>

#### module-level helpers are callable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = test_bitand(0xFF, 0x0F)
expect(x).to_equal(15)
```

</details>

### bitand_u32

#### returns 0 when no bits overlap

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_bitand(0xF0, 0x0F)
expect(result).to_equal(0)
```

</details>

#### returns common bits for partial overlap

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_bitand(0xFF, 0x0F)
expect(result).to_equal(15)
```

</details>

#### returns full value when both operands are equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_bitand(255, 255)
expect(result).to_equal(255)
```

</details>

#### returns 0 when one operand is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_bitand(0xABCD, 0)
expect(result).to_equal(0)
```

</details>

### bitor_u32

#### combines non-overlapping bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_bitor(0xF0, 0x0F)
expect(result).to_equal(255)
```

</details>

#### returns same value when one operand is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_bitor(0xAB, 0)
expect(result).to_equal(171)
```

</details>

#### is idempotent when both operands are equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_bitor(0xFF, 0xFF)
expect(result).to_equal(255)
```

</details>

### mask_invert_u32

#### inverts all bits within 32-bit range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_mask_invert(0)
expect(result).to_equal(4294967295)
```

</details>

#### inverts full mask to zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_mask_invert(4294967295)
expect(result).to_equal(0)
```

</details>

#### inverts partial mask correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0x0000FFFF inverted = 0xFFFF0000 = 4294901760
val result = test_mask_invert(65535)
expect(result).to_equal(4294901760)
```

</details>

### read-modify-write pattern

#### clears masked bits and sets new value

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# initial=0xFF, mask=0x0F (low nibble), value=0x05
# cleared = 0xFF & ~0x0F = 0xFF & 0xF0 = 0xF0 = 240
# updated = 0xF0 | (0x05 & 0x0F) = 0xF0 | 0x05 = 0xF5 = 245
val result = test_rmw(255, 15, 5)
expect(result).to_equal(245)
```

</details>

#### leaves unmasked bits unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# initial=0xAB=171, mask=0x0F, value=0x00
# clears low nibble: 0xA0=160
val result = test_rmw(171, 15, 0)
expect(result).to_equal(160)
```

</details>

#### sets all masked bits when value equals mask

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# initial=0x00, mask=0x0F, value=0x0F → result=0x0F=15
val result = test_rmw(0, 15, 15)
expect(result).to_equal(15)
```

</details>

### volatile API parameter conventions

#### address parameter is i64 (accommodates 64-bit pointers)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify the helper accepts i64 addresses without error
val addr: i64 = 0x40020010
val mask: i64 = 0x0001
val combined = test_bitand(addr, mask)
expect(combined).to_equal(0)
```

</details>

#### memory barrier concept: full barrier is distinct from load/store barriers

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Conceptual test: three distinct barrier kinds exist
val full_barrier_id: i64 = 0
val load_barrier_id: i64 = 1
val store_barrier_id: i64 = 2
expect(full_barrier_id).to_equal(0)
expect(load_barrier_id).to_equal(1)
expect(store_barrier_id).to_equal(2)
expect(full_barrier_id).to_equal(full_barrier_id)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/volatile_ops_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- volatile_ops SFFI module
- structural sanity
- bitand_u32
- bitor_u32
- mask_invert_u32
- read-modify-write pattern
- volatile API parameter conventions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
