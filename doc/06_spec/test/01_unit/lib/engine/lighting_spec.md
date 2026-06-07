# Lighting Specification

> <details>

<!-- sdn-diagram:id=lighting_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lighting_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lighting_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lighting_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lighting Specification

## Scenarios

### LightColor

#### creates white color

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = LightColor.white()
expect(c.r).to_equal(1.0)
expect(c.g).to_equal(1.0)
expect(c.b).to_equal(1.0)
```

</details>

#### creates warm color

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = LightColor.warm()
expect(c.r).to_equal(1.0)
expect(c.g).to_equal(0.9)
expect(c.b).to_equal(0.7)
```

</details>

#### creates cool color

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = LightColor.cool()
expect(c.r).to_equal(0.7)
expect(c.g).to_equal(0.85)
expect(c.b).to_equal(1.0)
```

</details>

#### scales intensity

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = LightColor.white()
val scaled = c.intensity_scaled(0.5)
expect(scaled.r).to_equal(0.5)
expect(scaled.g).to_equal(0.5)
expect(scaled.b).to_equal(0.5)
```

</details>

### DirectionalLight

#### creates with correct defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val light = DirectionalLight.new(0.0, -1.0, 0.0, LightColor.white(), 1.0)
expect(light.direction_x).to_equal(0.0)
expect(light.direction_y).to_equal(-1.0)
expect(light.direction_z).to_equal(0.0)
expect(light.intensity).to_equal(1.0)
expect(light.cast_shadows).to_equal(true)
expect(light.active).to_equal(true)
```

</details>

### PointLight

#### creates with correct fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val light = PointLight.new(1.0, 2.0, 3.0, LightColor.warm(), 0.8, 15.0)
expect(light.position_x).to_equal(1.0)
expect(light.position_y).to_equal(2.0)
expect(light.position_z).to_equal(3.0)
expect(light.intensity).to_equal(0.8)
expect(light.radius).to_equal(15.0)
expect(light.active).to_equal(true)
```

</details>

#### computes attenuation at zero distance

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val light = PointLight.new(0.0, 0.0, 0.0, LightColor.white(), 1.0, 10.0)
expect(light.attenuation_at(0.0)).to_equal(1.0)
```

</details>

#### returns zero attenuation beyond radius

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val light = PointLight.new(0.0, 0.0, 0.0, LightColor.white(), 1.0, 10.0)
expect(light.attenuation_at(11.0)).to_equal(0.0)
```

</details>

#### computes falloff within radius

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val light = PointLight.new(0.0, 0.0, 0.0, LightColor.white(), 1.0, 10.0)
val atten = light.attenuation_at(1.0)
# 1.0 / (1.0 + 1.0 * 1.0 * 1.0) = 0.5
expect(atten).to_equal(0.5)
```

</details>

### SpotLight

#### creates with correct fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val light = SpotLight.new(0.0, 5.0, 0.0, 0.0, -1.0, 0.0, 2.0, 0.3, 0.5, 20.0)
expect(light.position_y).to_equal(5.0)
expect(light.direction_y).to_equal(-1.0)
expect(light.intensity).to_equal(2.0)
expect(light.inner_angle).to_equal(0.3)
expect(light.outer_angle).to_equal(0.5)
expect(light.range).to_equal(20.0)
expect(light.active).to_equal(true)
```

</details>

### LightManager

#### starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = LightManager.new()
expect(mgr.directional_count()).to_equal(0)
expect(mgr.point_count()).to_equal(0)
expect(mgr.spot_count()).to_equal(0)
expect(mgr.total_light_count()).to_equal(0)
```

</details>

#### sets ambient light

1. var mgr = LightManager new
2. mgr set ambient
   - Expected: mgr.ambient_color.r equals `1.0`
   - Expected: mgr.ambient_color.g equals `0.9`
   - Expected: mgr.ambient_intensity equals `0.3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = LightManager.new()
mgr.set_ambient(LightColor.warm(), 0.3)
expect(mgr.ambient_color.r).to_equal(1.0)
expect(mgr.ambient_color.g).to_equal(0.9)
expect(mgr.ambient_intensity).to_equal(0.3)
```

</details>

#### adds directional light

1. var mgr = LightManager new
   - Expected: idx equals `0`
   - Expected: mgr.directional_count() equals `1`
   - Expected: mgr.total_light_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = LightManager.new()
val light = DirectionalLight.new(0.0, -1.0, 0.0, LightColor.white(), 1.0)
val idx = mgr.add_directional(light)
expect(idx).to_equal(0)
expect(mgr.directional_count()).to_equal(1)
expect(mgr.total_light_count()).to_equal(1)
```

</details>

#### adds point light

1. var mgr = LightManager new
   - Expected: idx equals `0`
   - Expected: mgr.point_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = LightManager.new()
val light = PointLight.new(0.0, 5.0, 0.0, LightColor.white(), 1.0, 10.0)
val idx = mgr.add_point(light)
expect(idx).to_equal(0)
expect(mgr.point_count()).to_equal(1)
```

</details>

#### adds spot light

1. var mgr = LightManager new
   - Expected: idx equals `0`
   - Expected: mgr.spot_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = LightManager.new()
val light = SpotLight.new(0.0, 5.0, 0.0, 0.0, -1.0, 0.0, 1.0, 0.3, 0.5, 20.0)
val idx = mgr.add_spot(light)
expect(idx).to_equal(0)
expect(mgr.spot_count()).to_equal(1)
```

</details>

#### removes point light

1. var mgr = LightManager new
2. mgr add point
3. mgr add point
   - Expected: mgr.point_count() equals `2`
   - Expected: removed is true
   - Expected: mgr.point_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = LightManager.new()
val l1 = PointLight.new(1.0, 0.0, 0.0, LightColor.white(), 1.0, 5.0)
val l2 = PointLight.new(2.0, 0.0, 0.0, LightColor.white(), 1.0, 5.0)
mgr.add_point(l1)
mgr.add_point(l2)
expect(mgr.point_count()).to_equal(2)
val removed = mgr.remove_point(0)
expect(removed).to_equal(true)
expect(mgr.point_count()).to_equal(1)
```

</details>

#### returns false for invalid remove index

1. var mgr = LightManager new
   - Expected: mgr.remove_point(0) is false
   - Expected: mgr.remove_point(-1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = LightManager.new()
expect(mgr.remove_point(0)).to_equal(false)
expect(mgr.remove_point(-1)).to_equal(false)
```

</details>

#### counts total lights across types

1. var mgr = LightManager new
2. mgr add directional
3. mgr add point
4. mgr add spot
   - Expected: mgr.total_light_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = LightManager.new()
mgr.add_directional(DirectionalLight.new(0.0, -1.0, 0.0, LightColor.white(), 1.0))
mgr.add_point(PointLight.new(0.0, 5.0, 0.0, LightColor.white(), 1.0, 10.0))
mgr.add_spot(SpotLight.new(0.0, 5.0, 0.0, 0.0, -1.0, 0.0, 1.0, 0.3, 0.5, 20.0))
expect(mgr.total_light_count()).to_equal(3)
```

</details>

#### clears all lights

1. var mgr = LightManager new
2. mgr add directional
3. mgr add point
4. mgr clear
   - Expected: mgr.total_light_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = LightManager.new()
mgr.add_directional(DirectionalLight.new(0.0, -1.0, 0.0, LightColor.white(), 1.0))
mgr.add_point(PointLight.new(0.0, 5.0, 0.0, LightColor.white(), 1.0, 10.0))
mgr.clear()
expect(mgr.total_light_count()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/lighting_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LightColor
- DirectionalLight
- PointLight
- SpotLight
- LightManager

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
