# Sprite Specification

> <details>

<!-- sdn-diagram:id=sprite_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sprite_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sprite_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sprite_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sprite Specification

## Scenarios

### Sprite

### create

#### stores texture_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Sprite.create(42, 10.0, 20.0, 32, 32)
expect(s.texture_id).to_equal(42)
```

</details>

#### stores position via transform

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Sprite.create(1, 10.0, 20.0, 64, 64)
val (wx, wy) = s.transform.world_position()
expect(wx).to_equal(10.0)
expect(wy).to_equal(20.0)
```

</details>

#### stores width and height

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Sprite.create(1, 0.0, 0.0, 48, 64)
expect(s.width).to_equal(48)
expect(s.height).to_equal(64)
```

</details>

#### defaults tint_color to white (0xFFFFFFFF)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Sprite.create(1, 0.0, 0.0, 32, 32)
expect(s.tint_color).to_equal(0xFFFFFFFF)
```

</details>

#### defaults z to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Sprite.create(1, 0.0, 0.0, 32, 32)
expect(s.z).to_equal(0.0)
```

</details>

#### defaults visible to true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Sprite.create(1, 0.0, 0.0, 16, 16)
expect(s.visible).to_equal(true)
```

</details>

### create_full

#### stores explicit z value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Sprite.create_full(2, 5.0, 10.0, 16, 16, 0.0, 0.0, 1.0, 1.0, 0xFFFF0000, 3.0)
expect(s.z).to_equal(3.0)
```

</details>

#### stores explicit tint_color

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Sprite.create_full(2, 0.0, 0.0, 16, 16, 0.0, 0.0, 1.0, 1.0, 0xFFFF0000, 0.0)
expect(s.tint_color).to_equal(0xFFFF0000)
```

</details>

### set_z

#### updates z field

1. var s = Sprite create
2. s set z
   - Expected: s.z equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = Sprite.create(1, 0.0, 0.0, 16, 16)
s.set_z(5.0)
expect(s.z).to_equal(5.0)
```

</details>

### set_visible

#### can hide sprite

1. var s = Sprite create
2. s set visible
   - Expected: s.visible is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = Sprite.create(1, 0.0, 0.0, 16, 16)
s.set_visible(false)
expect(s.visible).to_equal(false)
```

</details>

### FrameRef

### create

#### stores all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FrameRef.create(7, 0.0, 0.0, 0.5, 0.5)
expect(f.texture_id).to_equal(7)
expect(f.u1).to_equal(0.5)
expect(f.v1).to_equal(0.5)
```

</details>

### AnimatedSprite

### create

#### starts at frame 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f1 = FrameRef.create(1, 0.0, 0.0, 0.5, 1.0)
val f2 = FrameRef.create(1, 0.5, 0.0, 1.0, 1.0)
val anim = AnimatedSprite.create([f1, f2], 100.0, 0.0, 0.0, 32, 32)
expect(anim.current_frame).to_equal(0)
```

</details>

#### stores frame_duration_ms

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f1 = FrameRef.create(1, 0.0, 0.0, 1.0, 1.0)
val anim = AnimatedSprite.create([f1], 200.0, 0.0, 0.0, 16, 16)
expect(anim.frame_duration_ms).to_equal(200.0)
```

</details>

### tick

#### advances frame after duration elapses

1. var anim = AnimatedSprite create
2. anim tick
   - Expected: anim.current_frame equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f1 = FrameRef.create(1, 0.0, 0.0, 0.5, 1.0)
val f2 = FrameRef.create(1, 0.5, 0.0, 1.0, 1.0)
var anim = AnimatedSprite.create([f1, f2], 100.0, 0.0, 0.0, 32, 32)
anim.tick(110.0)
expect(anim.current_frame).to_equal(1)
```

</details>

#### wraps back to frame 0 after last frame

1. var anim = AnimatedSprite create
2. anim tick
3. anim tick
   - Expected: anim.current_frame equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f1 = FrameRef.create(1, 0.0, 0.0, 0.5, 1.0)
val f2 = FrameRef.create(1, 0.5, 0.0, 1.0, 1.0)
var anim = AnimatedSprite.create([f1, f2], 100.0, 0.0, 0.0, 32, 32)
anim.tick(110.0)
anim.tick(110.0)
expect(anim.current_frame).to_equal(0)
```

</details>

#### does not advance when not playing

1. var anim = AnimatedSprite create
2. anim stop
3. anim tick
   - Expected: anim.current_frame equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f1 = FrameRef.create(1, 0.0, 0.0, 0.5, 1.0)
val f2 = FrameRef.create(1, 0.5, 0.0, 1.0, 1.0)
var anim = AnimatedSprite.create([f1, f2], 100.0, 0.0, 0.0, 32, 32)
anim.stop()
anim.tick(200.0)
expect(anim.current_frame).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/game2d/sprite_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Sprite
- create
- create_full
- set_z
- set_visible
- FrameRef
- create
- AnimatedSprite
- create
- tick

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
