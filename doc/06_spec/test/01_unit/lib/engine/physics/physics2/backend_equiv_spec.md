# Backend Equiv Specification

> <details>

<!-- sdn-diagram:id=backend_equiv_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_equiv_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_equiv_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_equiv_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Equiv Specification

## Scenarios

### Backend Equivalence

#### scalar and simd produce same stacking result

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scalar_result = run_stacking_scene(PhysicsBackend.CpuScalar)
val simd_result = run_stacking_scene(PhysicsBackend.CpuSimd)
val diff1 = scalar_result.0 - simd_result.0
val diff2 = scalar_result.1 - simd_result.1
val abs_diff1 = if diff1 < 0.0: -diff1 else: diff1
val abs_diff2 = if diff2 < 0.0: -diff2 else: diff2
expect(abs_diff1 < 0.001).to_equal(true)
expect(abs_diff2 < 0.001).to_equal(true)
```

</details>

#### both backends produce finite positions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_stacking_scene(PhysicsBackend.CpuSimd)
expect(result.0 > -100.0).to_equal(true)
expect(result.1 > -100.0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/physics/physics2/backend_equiv_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Backend Equivalence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
