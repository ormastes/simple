# Scene Specification

> <details>

<!-- sdn-diagram:id=scene_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scene_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scene_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scene_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scene Specification

## Scenarios

### Scene

### create

#### starts with no children

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sc = Scene.create()
expect(sc.child_count()).to_equal(0)
```

</details>

#### is visible by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sc = Scene.create()
expect(sc.visible).to_equal(true)
```

</details>

### add_sprite

#### increases child count

1. var sc = Scene create
2. sc add sprite
   - Expected: sc.child_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sc = Scene.create()
sc.add_sprite(Sprite.create(1, 0.0, 0.0, 8, 8))
expect(sc.child_count()).to_equal(1)
```

</details>

#### accumulates multiple sprites

1. var sc = Scene create
2. sc add sprite
3. sc add sprite
   - Expected: sc.child_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sc = Scene.create()
sc.add_sprite(Sprite.create(1, 0.0, 0.0, 8, 8))
sc.add_sprite(Sprite.create(2, 10.0, 10.0, 8, 8))
expect(sc.child_count()).to_equal(2)
```

</details>

### render

#### renders two sprites onto a CPU engine without error

1. var sc = Scene create
2. var s1 = Sprite create
3. var s2 = Sprite create
4. s1 set tint
5. s2 set tint
6. sc add sprite
7. sc add sprite
8. var engine = Engine2D create with backend
9. engine clear
10. sc render
11. engine present
   - Expected: pixels.len() equals `64 * 64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sc = Scene.create()
var s1 = Sprite.create(1, 0.0, 0.0, 4, 4)
var s2 = Sprite.create(2, 8.0, 8.0, 4, 4)
s1.set_tint(0xFFFF0000)   # red
s2.set_tint(0xFF0000FF)   # blue
sc.add_sprite(s1)
sc.add_sprite(s2)
var engine = Engine2D.create_with_backend(64, 64, "cpu")
engine.clear(0xFF000000)
val cam = Camera2D.create(0.0, 0.0, 64.0, 64.0)
sc.render(engine, cam)
engine.present()
val pixels = engine.read_pixels()
expect(pixels.len()).to_equal(64 * 64)
```

</details>

#### produces red pixels from a red sprite

1. var sc = Scene create
2. var s = Sprite create
3. s set tint
4. sc add sprite
5. var engine = Engine2D create with backend
6. engine clear
7. sc render
8. engine present
   - Expected: found_red is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sc = Scene.create()
var s = Sprite.create(1, -32.0, -32.0, 8, 8)
s.set_tint(0xFFFF0000)
sc.add_sprite(s)
var engine = Engine2D.create_with_backend(64, 64, "cpu")
engine.clear(0xFF000000)
val cam = Camera2D.create(0.0, 0.0, 64.0, 64.0)
sc.render(engine, cam)
engine.present()
val pixels = engine.read_pixels()
var found_red = false
var i = 0
while i < pixels.len():
    if pixels[i] == 0xFFFF0000:
        found_red = true
    i = i + 1
expect(found_red).to_equal(true)
```

</details>

#### invisible scene skips drawing

1. var sc = Scene create
2. var s = Sprite create
3. s set tint
4. sc add sprite
5. var engine = Engine2D create with backend
6. engine clear
7. sc render
8. engine present
   - Expected: found_non_black is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sc = Scene.create()
sc.visible = false
var s = Sprite.create(1, -32.0, -32.0, 8, 8)
s.set_tint(0xFFFF0000)
sc.add_sprite(s)
var engine = Engine2D.create_with_backend(32, 32, "cpu")
engine.clear(0xFF000000)
val cam = Camera2D.create(0.0, 0.0, 32.0, 32.0)
sc.render(engine, cam)
engine.present()
val pixels = engine.read_pixels()
var found_non_black = false
var i = 0
while i < pixels.len():
    if pixels[i] != 0xFF000000:
        found_non_black = true
    i = i + 1
expect(found_non_black).to_equal(false)
```

</details>

### nested scene

#### renders child scene sprites

1. var parent = Scene create
2. var child = Scene create
3. var s = Sprite create
4. s set tint
5. child add sprite
6. parent add scene
7. var engine = Engine2D create with backend
8. engine clear
9. parent render
10. engine present
   - Expected: found_green is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parent = Scene.create()
var child = Scene.create()
var s = Sprite.create(1, -16.0, -16.0, 4, 4)
s.set_tint(0xFF00FF00)
child.add_sprite(s)
parent.add_scene(child)
var engine = Engine2D.create_with_backend(64, 64, "cpu")
engine.clear(0xFF000000)
val cam = Camera2D.create(0.0, 0.0, 64.0, 64.0)
parent.render(engine, cam)
engine.present()
val pixels = engine.read_pixels()
var found_green = false
var i = 0
while i < pixels.len():
    if pixels[i] == 0xFF00FF00:
        found_green = true
    i = i + 1
expect(found_green).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/game2d/scene_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Scene
- create
- add_sprite
- render
- nested scene

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
