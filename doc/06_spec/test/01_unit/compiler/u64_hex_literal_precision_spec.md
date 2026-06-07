# U64 Hex Literal Precision Specification

> 1. var v: u64 = top bit

<!-- sdn-diagram:id=u64_hex_literal_precision_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=u64_hex_literal_precision_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

u64_hex_literal_precision_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=u64_hex_literal_precision_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# U64 Hex Literal Precision Specification

## Scenarios

### u64 hex literal precision

#### preserves bit 63 (top bit only)

1. var v: u64 = top bit
   - Expected: v equals `9223372036854775808u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var v: u64 = top_bit()
expect(v).to_equal(9223372036854775808u64)
```

</details>

#### preserves all-ones (max u64)

1. var v: u64 = all ones
   - Expected: v equals `18446744073709551615u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var v: u64 = all_ones()
expect(v).to_equal(18446744073709551615u64)
```

</details>

#### preserves arbitrary 64-bit pattern

1. var v: u64 = cafe babe
   - Expected: v equals `14627333968688430831u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var v: u64 = cafe_babe()
expect(v).to_equal(14627333968688430831u64)
```

</details>

#### preserves SHA-512 IV constant

1. var v: u64 = sha512 iv
   - Expected: v equals `7640891576956012808u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var v: u64 = sha512_iv()
expect(v).to_equal(7640891576956012808u64)
```

</details>

#### preserves SHA-384 IV5 constant (bit 63 set)

1. var v: u64 = sha384 iv5
   - Expected: v equals `15784041429090275239u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var v: u64 = sha384_iv5()
expect(v).to_equal(15784041429090275239u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/u64_hex_literal_precision_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- u64 hex literal precision

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
