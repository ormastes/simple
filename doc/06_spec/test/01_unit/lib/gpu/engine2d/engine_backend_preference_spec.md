# Engine Backend Preference Specification

> <details>

<!-- sdn-diagram:id=engine_backend_preference_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine_backend_preference_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine_backend_preference_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine_backend_preference_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Backend Preference Specification

## Scenarios

### Engine2D backend preference

#### exposes compact GUI startup order before CPU fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val order = Engine2D.preferred_backend_order()

expect(order.len()).to_equal(8)
expect(order[0]).to_equal("metal")
expect(order[1]).to_equal("cuda")
expect(order[2]).to_equal("rocm")
expect(order[3]).to_equal("vulkan")
expect(order[4]).to_equal("opencl")
expect(order[5]).to_equal("software")
expect(order[6]).to_equal("cpu_simd")
expect(order[7]).to_equal("cpu")
expect(Engine2D.preferred_backend_order_summary()).to_equal("metal > cuda > rocm/hip > vulkan > opencl > software > cpu_simd > cpu")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/engine_backend_preference_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D backend preference

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
