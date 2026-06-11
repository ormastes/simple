# Overflow Debug Specification

> <details>

<!-- sdn-diagram:id=overflow_debug_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=overflow_debug_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

overflow_debug_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=overflow_debug_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Overflow Debug Specification

## Scenarios

### i64 overflow behavior

#### max i64 + 1 wraps to min

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val max = 9223372036854775807
val result = max + 1
expect(result).to_equal(-9223372036854775808)
```

</details>

#### large left shift stays in 64 bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1
val shifted = x << 63
# Should be -9223372036854775808 (min i64, bit 63 set)
expect(shifted).to_equal(-9223372036854775808)
```

</details>

#### mask with -1 works as no-op

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 100
val r = x & -1
expect(r).to_equal(100)
```

</details>

#### two large values add with wrap

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 9223372036854775807
val b = 9223372036854775807
val r = a + b
expect(r).to_equal(-2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/overflow_debug_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- i64 overflow behavior

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
