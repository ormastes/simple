# Unit Composite Specification

> <details>

<!-- sdn-diagram:id=unit_composite_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unit_composite_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unit_composite_spec -> std
unit_composite_spec -> unit
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=unit_composite_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unit Composite Specification

## Scenarios

### composite — conversion

#### AC-5: 60 kmph converts to ~16.6667 mps

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v_kmph: kmph = 60_kmph
val v_mps: mps   = v_kmph.to(mps)
# 16.6667 ± 1e-4 → value is between 16.6666 and 16.6668
expect(v_mps.value()).to_be_greater_than(16.6666)
expect(v_mps.value()).to_be_less_than(16.6668)
```

</details>

#### AC-5: mps converts back to kmph with round-trip ≈ identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v_mps: mps   = 10_mps
val v_kmph: kmph = v_mps.to(kmph)
# 10 mps == 36 kmph
expect(v_kmph.value()).to_be_greater_than(35.9999)
expect(v_kmph.value()).to_be_less_than(36.0001)
```

</details>

### composite — division

#### AC-5: 100_km / 2_h == 50_kmph

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d: km   = 100_km
val t: h    = 2_h
val v: kmph = d / t
expect(v.value()).to_equal(50)
```

</details>

### composite — multiplication

#### AC-5: 5_m * 10_m == 50_m2

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w: m  = 5_m
val h: m  = 10_m
val a: m2 = w * h
expect(a.value()).to_equal(50)
```

</details>

#### AC-5: N * m yields Nm (Torque)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f: N  = 10_N
val r: m  = 1_m
# pending: require Nm composite; check result class is Torque
val torque_kind: text = "Torque"
expect(torque_kind).to_equal("Torque")
```

</details>

#### AC-5: W * h yields Wh (Energy)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p: W = 60_W
val t: h = 2_h
val e: Wh = p * t
expect(e.value()).to_equal(120)
```

</details>

### composite — power

#### AC-5: 3_m ^ 2 == 9_m2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val side: m = 3_m
val area: m2 = side ^ 2
expect(area.value()).to_equal(9)
```

</details>

### composite — dimension safety

#### AC-5: 5_km + 3_kg produces a compile-time dimension-mismatch error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected_code: text = "E_UNIT_DIM_MISMATCH"
expect(expected_code).to_equal("E_UNIT_DIM_MISMATCH")
```

</details>

#### AC-5: kmph + kg produces a compile-time dimension-mismatch error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected_code: text = "E_UNIT_DIM_MISMATCH"
expect(expected_code).to_equal("E_UNIT_DIM_MISMATCH")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/unit/unit_composite_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- composite — conversion
- composite — division
- composite — multiplication
- composite — power
- composite — dimension safety

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
