# Occlusion Specification

> <details>

<!-- sdn-diagram:id=occlusion_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=occlusion_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

occlusion_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=occlusion_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Occlusion Specification

## Scenarios

### Occlusion — no hits

#### zero hits returns 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_occlusion_config()
val listener = Vec2(x: 0.0, y: 0.0)
val source = Vec2(x: 10.0, y: 0.0)
val mult = compute_occlusion_2d(listener, source, 0, config)
expect(mult > 0.99).to_equal(true)
expect(mult < 1.01).to_equal(true)
```

</details>

### Occlusion — one hit

#### one hit with attenuation 0.5 returns 0.5

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_occlusion_config()
val listener = Vec2(x: 0.0, y: 0.0)
val source = Vec2(x: 10.0, y: 0.0)
val mult = compute_occlusion_2d(listener, source, 1, config)
expect(mult > 0.49).to_equal(true)
expect(mult < 0.51).to_equal(true)
```

</details>

### Occlusion — two hits

#### two hits with attenuation 0.5 returns 0.25

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_occlusion_config()
val listener = Vec2(x: 0.0, y: 0.0)
val source = Vec2(x: 10.0, y: 0.0)
val mult = compute_occlusion_2d(listener, source, 2, config)
expect(mult > 0.24).to_equal(true)
expect(mult < 0.26).to_equal(true)
```

</details>

### Occlusion — disabled

#### disabled occlusion returns 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = OcclusionConfig(enabled: false, max_ray_distance: 1000.0, attenuation_per_hit: 0.5)
val listener = Vec2(x: 0.0, y: 0.0)
val source = Vec2(x: 10.0, y: 0.0)
val mult = compute_occlusion_2d(listener, source, 3, config)
expect(mult > 0.99).to_equal(true)
expect(mult < 1.01).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/occlusion_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Occlusion — no hits
- Occlusion — one hit
- Occlusion — two hits
- Occlusion — disabled

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
