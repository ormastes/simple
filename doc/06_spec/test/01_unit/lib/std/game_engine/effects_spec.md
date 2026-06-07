# Effects Specification

> 1. expect effect is GameEffect RenderEffect

<!-- sdn-diagram:id=effects_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=effects_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

effects_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=effects_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Effects Specification

## Scenarios

### GameEffect

#### creates RenderEffect

1. expect effect is GameEffect RenderEffect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val effect = GameEffect.RenderEffect("draw_sprite")
expect effect is GameEffect.RenderEffect(_)
```

</details>

#### creates PhysicsEffect

1. expect effect is GameEffect PhysicsEffect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val effect = GameEffect.PhysicsEffect("apply_force")
expect effect is GameEffect.PhysicsEffect(_)
```

</details>

#### creates AudioEffect

1. expect effect is GameEffect AudioEffect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val effect = GameEffect.AudioEffect("play_sound")
expect effect is GameEffect.AudioEffect(_)
```

</details>

#### creates IOEffect

1. expect effect is GameEffect IOEffect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val effect = GameEffect.IOEffect("load_asset")
expect effect is GameEffect.IOEffect(_)
```

</details>

#### creates EngineSyncEffect

1. expect effect is GameEffect EngineSyncEffect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val effect = GameEffect.EngineSyncEffect("update_scene")
expect effect is GameEffect.EngineSyncEffect(_)
```

</details>

### EffectContext

#### creation

#### creates empty context

1. expect ctx is empty
2. expect ctx effect count


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = EffectContext.new()
expect ctx.is_empty()
expect ctx.effect_count() == 0
```

</details>

#### starts as async safe

1. expect ctx is async safe


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = EffectContext.new()
expect ctx.is_async_safe()
```

</details>

#### effect management

#### adds effects

1. var ctx = EffectContext new
2. ctx add effect
3. expect ctx has effects
4. expect ctx effect count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = EffectContext.new()
ctx.add_effect(GameEffect.RenderEffect("draw"))
expect ctx.has_effects()
expect ctx.effect_count() == 1
```

</details>

#### checks for specific effect

1. var ctx = EffectContext new
2. ctx add effect
3. expect ctx has effect
4. expect not ctx has effect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = EffectContext.new()
ctx.add_effect(GameEffect.PhysicsEffect("collision"))
expect ctx.has_effect("collision")
expect not ctx.has_effect("other")
```

</details>

#### async safety

#### remains async safe with render effects

1. var ctx = EffectContext new
2. ctx add effect
3. expect ctx is async safe


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = EffectContext.new()
ctx.add_effect(GameEffect.RenderEffect("draw"))
expect ctx.is_async_safe()
```

</details>

#### becomes unsafe with sync effects

1. var ctx = EffectContext new
2. ctx add effect
3. expect not ctx is async safe


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = EffectContext.new()
ctx.add_effect(GameEffect.EngineSyncEffect("main_thread_op"))
expect not ctx.is_async_safe()
```

</details>

#### summary

#### provides context summary

1. var ctx = EffectContext new
2. ctx add effect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = EffectContext.new()
ctx.add_effect(GameEffect.RenderEffect("draw"))
val summary = ctx.summary()
expect "1 effects" in summary or "1 effect" in summary
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/game_engine/effects_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GameEffect
- EffectContext

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
