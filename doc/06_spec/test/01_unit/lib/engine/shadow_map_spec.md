# Shadow Map Specification

> <details>

<!-- sdn-diagram:id=shadow_map_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shadow_map_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shadow_map_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shadow_map_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shadow Map Specification

## Scenarios

### ShadowMapConfig

#### creates default config

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = ShadowMapConfig.default_config()
expect(cfg.resolution).to_equal(1024)
expect(cfg.bias).to_equal(0.005)
expect(cfg.normal_bias).to_equal(0.02)
expect(cfg.soft_shadows).to_equal(true)
```

</details>

#### creates high quality config

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = ShadowMapConfig.high_quality()
expect(cfg.resolution).to_equal(2048)
expect(cfg.bias).to_equal(0.003)
expect(cfg.normal_bias).to_equal(0.01)
expect(cfg.soft_shadows).to_equal(true)
```

</details>

### CascadedShadowMap

#### creates with correct cascade count

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = ShadowMapConfig.default_config()
val csm = CascadedShadowMap.new(4, cfg)
expect(csm.cascade_count).to_equal(4)
expect(csm.cascades.len()).to_equal(4)
```

</details>

#### generates increasing split distances

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = ShadowMapConfig.default_config()
val csm = CascadedShadowMap.new(3, cfg)
val c0 = csm.cascades[0]
val c1 = csm.cascades[1]
val c2 = csm.cascades[2]
expect(c0.split_distance < c1.split_distance).to_equal(true)
expect(c1.split_distance < c2.split_distance).to_equal(true)
```

</details>

#### gets cascade by valid index

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = ShadowMapConfig.default_config()
val csm = CascadedShadowMap.new(2, cfg)
val maybe = csm.get_cascade(0)
if val Some(level) = maybe:
    expect(level.split_distance > 0.0).to_equal(true)
```

</details>

#### returns None for invalid cascade index

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = ShadowMapConfig.default_config()
val csm = CascadedShadowMap.new(2, cfg)
val maybe = csm.get_cascade(5)
if val Some(level) = maybe:
    expect(1).to_equal(0)
```

</details>

#### computes total resolution

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = ShadowMapConfig.default_config()
val csm = CascadedShadowMap.new(2, cfg)
val total = csm.total_resolution()
# First cascade: 1024, second: 512
expect(total).to_equal(1536)
```

</details>

### ShadowSystem

#### starts enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = ShadowMapConfig.default_config()
val sys = ShadowSystem.new(cfg)
expect(sys.is_enabled()).to_equal(true)
expect(sys.shadow_map_count()).to_equal(0)
```

</details>

#### adds shadow maps

1. var sys = ShadowSystem new
   - Expected: idx equals `0`
   - Expected: sys.shadow_map_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = ShadowMapConfig.default_config()
var sys = ShadowSystem.new(cfg)
val csm = CascadedShadowMap.new(3, cfg)
val idx = sys.add_shadow_map(csm)
expect(idx).to_equal(0)
expect(sys.shadow_map_count()).to_equal(1)
```

</details>

#### toggles enabled state

1. var sys = ShadowSystem new
2. sys set enabled
   - Expected: sys.is_enabled() is false
3. sys set enabled
   - Expected: sys.is_enabled() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = ShadowMapConfig.default_config()
var sys = ShadowSystem.new(cfg)
sys.set_enabled(false)
expect(sys.is_enabled()).to_equal(false)
sys.set_enabled(true)
expect(sys.is_enabled()).to_equal(true)
```

</details>

#### clears all shadow maps

1. var sys = ShadowSystem new
2. sys add shadow map
3. sys add shadow map
   - Expected: sys.shadow_map_count() equals `2`
4. sys clear
   - Expected: sys.shadow_map_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = ShadowMapConfig.default_config()
var sys = ShadowSystem.new(cfg)
sys.add_shadow_map(CascadedShadowMap.new(2, cfg))
sys.add_shadow_map(CascadedShadowMap.new(4, cfg))
expect(sys.shadow_map_count()).to_equal(2)
sys.clear()
expect(sys.shadow_map_count()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/shadow_map_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ShadowMapConfig
- CascadedShadowMap
- ShadowSystem

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
