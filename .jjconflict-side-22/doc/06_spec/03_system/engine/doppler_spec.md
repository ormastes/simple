# Doppler Specification

> <details>

<!-- sdn-diagram:id=doppler_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=doppler_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

doppler_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=doppler_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Doppler Specification

## Scenarios

### Doppler — stationary

#### stationary listener and source gives pitch 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_doppler_config()
val zero = Vec3(x: 0.0, y: 0.0, z: 0.0)
val pos = Vec3(x: 10.0, y: 0.0, z: 0.0)
val pitch = compute_doppler_pitch(zero, zero, pos, zero, config)
expect(pitch > 0.99).to_equal(true)
expect(pitch < 1.01).to_equal(true)
```

</details>

### Doppler — source moving toward listener

#### pitch is greater than 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_doppler_config()
val l_pos = Vec3(x: 0.0, y: 0.0, z: 0.0)
val l_vel = Vec3(x: 0.0, y: 0.0, z: 0.0)
val s_pos = Vec3(x: 100.0, y: 0.0, z: 0.0)
val s_vel = Vec3(x: -50.0, y: 0.0, z: 0.0)
val pitch = compute_doppler_pitch(l_pos, l_vel, s_pos, s_vel, config)
expect(pitch > 1.0).to_equal(true)
```

</details>

### Doppler — source moving away from listener

#### pitch is less than 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_doppler_config()
val l_pos = Vec3(x: 0.0, y: 0.0, z: 0.0)
val l_vel = Vec3(x: 0.0, y: 0.0, z: 0.0)
val s_pos = Vec3(x: 100.0, y: 0.0, z: 0.0)
val s_vel = Vec3(x: 50.0, y: 0.0, z: 0.0)
val pitch = compute_doppler_pitch(l_pos, l_vel, s_pos, s_vel, config)
expect(pitch < 1.0).to_equal(true)
```

</details>

### Doppler — disabled

#### disabled doppler returns 1.0 regardless of velocities

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = DopplerConfig(enabled: false, speed_of_sound: 343.0, factor: 1.0)
val l_pos = Vec3(x: 0.0, y: 0.0, z: 0.0)
val l_vel = Vec3(x: 0.0, y: 0.0, z: 0.0)
val s_pos = Vec3(x: 100.0, y: 0.0, z: 0.0)
val s_vel = Vec3(x: -50.0, y: 0.0, z: 0.0)
val pitch = compute_doppler_pitch(l_pos, l_vel, s_pos, s_vel, config)
expect(pitch > 0.99).to_equal(true)
expect(pitch < 1.01).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/doppler_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Doppler — stationary
- Doppler — source moving toward listener
- Doppler — source moving away from listener
- Doppler — disabled

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
