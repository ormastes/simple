# color_spec

> Engine Color — EngineColor Tests

<!-- sdn-diagram:id=color_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=color_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

color_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=color_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# color_spec

Engine Color — EngineColor Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/color_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Color — EngineColor Tests

Tests RGBA constructors, presets, lerp, to_rgba8, from_hex.

## Scenarios

### EngineColor

### constructors

#### creates RGBA color

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = EngineColor.rgba(0.5, 0.6, 0.7, 0.8)
expect(c.r).to_equal(0.5)
expect(c.g).to_equal(0.6)
expect(c.b).to_equal(0.7)
expect(c.a).to_equal(0.8)
```

</details>

#### creates RGB color with alpha 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = EngineColor.rgb(0.1, 0.2, 0.3)
expect(c.a).to_equal(1.0)
```

</details>

### presets

#### creates white

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = EngineColor.white()
expect(c.r).to_equal(1.0)
expect(c.g).to_equal(1.0)
expect(c.b).to_equal(1.0)
```

</details>

#### creates black

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = EngineColor.black()
expect(c.r).to_equal(0.0)
expect(c.g).to_equal(0.0)
expect(c.b).to_equal(0.0)
```

</details>

#### creates red

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = EngineColor.red()
expect(c.r).to_equal(1.0)
expect(c.g).to_equal(0.0)
expect(c.b).to_equal(0.0)
```

</details>

### operations

#### lerps between two colors at t=0.5

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = EngineColor.black()
val b = EngineColor.white()
val mid = a.lerp(b, 0.5)
# Each channel should be ~0.5
val ri = mid.r * 1000.0
expect(ri).to_be_greater_than(499.0)
expect(ri).to_be_less_than(501.0)
```

</details>

#### converts to rgba8 struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = EngineColor.rgba(1.0, 0.0, 0.5, 1.0)
val rgba = c.to_rgba8()
expect(rgba.r).to_equal(255)
expect(rgba.g).to_equal(0)
# 0.5 * 255 ~= 128
expect(rgba.b).to_be_greater_than(126)
expect(rgba.b).to_be_less_than(129)
expect(rgba.a).to_equal(255)
```

</details>

#### creates from hex integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0xFF0000 = red (255, 0, 0)
val c = EngineColor.from_hex(16711680)
expect(c.r).to_equal(1.0)
expect(c.g).to_equal(0.0)
expect(c.b).to_equal(0.0)
```

</details>

#### creates color with modified alpha

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = EngineColor.red()
val faded = c.with_alpha(0.5)
expect(faded.r).to_equal(1.0)
expect(faded.a).to_equal(0.5)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
