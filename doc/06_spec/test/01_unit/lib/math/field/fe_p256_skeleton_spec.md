# Fe P256 Skeleton Specification

> <details>

<!-- sdn-diagram:id=fe_p256_skeleton_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fe_p256_skeleton_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fe_p256_skeleton_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fe_p256_skeleton_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fe P256 Skeleton Specification

## Scenarios

### FeP256 — skeleton constants

#### fe_zero encodes to 32 zero bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = fe_to_bytes(fe_zero())
var ok = true
var i: u64 = 0
while i < 32:
    if out[i] != 0x00:
        ok = false
    i = i + 1
expect(ok).to_equal(true)
```

</details>

#### fe_one encodes to 31 zeros followed by 0x01 (big-endian)

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = fe_to_bytes(fe_one())
var ok = true
var i: u64 = 0
while i < 31:
    if out[i] != 0x00:
        ok = false
    i = i + 1
expect(ok).to_equal(true)
expect(out[31]).to_equal(0x01)
```

</details>

### FeP256 — skeleton byte round-trip

#### Gx round-trips through fe_from_bytes / fe_to_bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = _gx_bytes()
val fe = fe_from_bytes(b)
val out = fe_to_bytes(fe)
expect(_bytes_eq(out, b)).to_equal(true)
```

</details>

#### Gy round-trips through fe_from_bytes / fe_to_bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = _gy_bytes()
val fe = fe_from_bytes(b)
val out = fe_to_bytes(fe)
expect(_bytes_eq(out, b)).to_equal(true)
```

</details>

### FeP256 — skeleton equality

#### fe_eq is reflexive on a decoded point

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = fe_from_bytes(_gx_bytes())
expect(fe_eq(a, a)).to_equal(true)
```

</details>

#### fe_eq returns false for Gx vs Gy

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = fe_from_bytes(_gx_bytes())
val b = fe_from_bytes(_gy_bytes())
expect(fe_eq(a, b)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/math/field/fe_p256_skeleton_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FeP256 — skeleton constants
- FeP256 — skeleton byte round-trip
- FeP256 — skeleton equality

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
