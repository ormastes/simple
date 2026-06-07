# Unsigned To I64 Specification

> 1. xs push

<!-- sdn-diagram:id=unsigned_to_i64_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unsigned_to_i64_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unsigned_to_i64_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=unsigned_to_i64_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unsigned To I64 Specification

## Scenarios

### unsigned integer to_i64

#### preserves u8 values pushed into arrays

1. xs push
2. xs push
3. xs push
4. xs push
5. xs push
6. xs push
7. xs push
   - Expected: xs[0].to_i64() equals `0`
   - Expected: xs[1].to_i64() equals `1`
   - Expected: xs[2].to_i64() equals `2`
   - Expected: xs[3].to_i64() equals `4`
   - Expected: xs[4].to_i64() equals `8`
   - Expected: xs[5].to_i64() equals `16`
   - Expected: xs[6].to_i64() equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var xs: [u8] = []
xs.push(0u8)
xs.push(1u8)
xs.push(2u8)
xs.push(4u8)
xs.push(8u8)
xs.push(16u8)
xs.push(255u8)

expect(xs[0].to_i64()).to_equal(0)
expect(xs[1].to_i64()).to_equal(1)
expect(xs[2].to_i64()).to_equal(2)
expect(xs[3].to_i64()).to_equal(4)
expect(xs[4].to_i64()).to_equal(8)
expect(xs[5].to_i64()).to_equal(16)
expect(xs[6].to_i64()).to_equal(255)
```

</details>

#### preserves TLS vector hex u8 literals

1. salt push
2. salt push
3. salt push
4. salt push
5. salt push
6. salt push
7. salt push
8. salt push
9. salt push
10. salt push
11. salt push
12. salt push
13. salt push
   - Expected: salt[8].to_i64() equals `8`
   - Expected: salt[9].to_i64() equals `9`
   - Expected: salt[10].to_i64() equals `10`
   - Expected: salt[11].to_i64() equals `11`
   - Expected: salt[12].to_i64() equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var salt: [u8] = []
salt.push(0x00u8)
salt.push(0x01u8)
salt.push(0x02u8)
salt.push(0x03u8)
salt.push(0x04u8)
salt.push(0x05u8)
salt.push(0x06u8)
salt.push(0x07u8)
salt.push(0x08u8)
salt.push(0x09u8)
salt.push(0x0au8)
salt.push(0x0bu8)
salt.push(0x0cu8)

expect(salt[8].to_i64()).to_equal(8)
expect(salt[9].to_i64()).to_equal(9)
expect(salt[10].to_i64()).to_equal(10)
expect(salt[11].to_i64()).to_equal(11)
expect(salt[12].to_i64()).to_equal(12)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/unsigned_to_i64_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- unsigned integer to_i64

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
