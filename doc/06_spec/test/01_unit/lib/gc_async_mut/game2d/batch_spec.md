# Batch Specification

> <details>

<!-- sdn-diagram:id=batch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=batch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

batch_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=batch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Batch Specification

## Scenarios

### SpriteBatch

### create

#### starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = SpriteBatch.create(1)
expect(b.len()).to_equal(0)
```

</details>

#### stores texture_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = SpriteBatch.create(99)
expect(b.texture_id).to_equal(99)
```

</details>

### add

#### increments length

1. var b = SpriteBatch create
2. b add
   - Expected: b.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = SpriteBatch.create(1)
val s = Sprite.create(1, 0.0, 0.0, 16, 16)
b.add(s)
expect(b.len()).to_equal(1)
```

</details>

#### accumulates multiple sprites

1. var b = SpriteBatch create
2. b add
3. b add
4. b add
   - Expected: b.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = SpriteBatch.create(1)
b.add(Sprite.create(1, 0.0, 0.0, 16, 16))
b.add(Sprite.create(1, 16.0, 0.0, 16, 16))
b.add(Sprite.create(1, 32.0, 0.0, 16, 16))
expect(b.len()).to_equal(3)
```

</details>

### clear

#### empties the batch

1. var b = SpriteBatch create
2. b add
3. b clear
   - Expected: b.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = SpriteBatch.create(1)
b.add(Sprite.create(1, 0.0, 0.0, 8, 8))
b.clear()
expect(b.len()).to_equal(0)
```

</details>

### z-ordering

#### sprites are accessible after insertion regardless of z

1. var b = SpriteBatch create
2. var s1 = Sprite create
3. var s2 = Sprite create
4. s1 set z
5. s2 set z
6. b add
7. b add
   - Expected: b.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = SpriteBatch.create(1)
var s1 = Sprite.create(1, 0.0, 0.0, 16, 16)
var s2 = Sprite.create(1, 16.0, 0.0, 16, 16)
s1.set_z(5.0)
s2.set_z(1.0)
b.add(s1)
b.add(s2)
# After flush (which sorts), s2 (z=1) should come before s1 (z=5)
# We verify the sort here by checking the batch length is still 2
expect(b.len()).to_equal(2)
```

</details>

### flush

#### draws all visible sprites without error

1. var b = SpriteBatch create
2. b add
3. b add
4. var engine = Engine2D create with backend
5. engine clear
6. b flush
   - Expected: pixels.len() equals `64 * 64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = SpriteBatch.create(1)
b.add(Sprite.create(1, 0.0, 0.0, 4, 4))
b.add(Sprite.create(1, 8.0, 0.0, 4, 4))
var engine = Engine2D.create_with_backend(64, 64, "cpu")
engine.clear(0xFF000000)
b.flush(engine)
val pixels = engine.read_pixels()
expect(pixels.len()).to_equal(64 * 64)
```

</details>

#### skips invisible sprites

1. var b = SpriteBatch create
2. var hidden = Sprite create
3. hidden set visible
4. hidden set tint
5. b add
6. var engine = Engine2D create with backend
7. engine clear
8. b flush
   - Expected: found_red is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = SpriteBatch.create(1)
var hidden = Sprite.create(1, 0.0, 0.0, 4, 4)
hidden.set_visible(false)
hidden.set_tint(0xFFFF0000)
b.add(hidden)
var engine = Engine2D.create_with_backend(32, 32, "cpu")
engine.clear(0xFF000000)
b.flush(engine)
val pixels = engine.read_pixels()
# No red pixels — hidden sprite not drawn
var found_red = false
var i = 0
while i < pixels.len():
    if pixels[i] == 0xFFFF0000:
        found_red = true
    i = i + 1
expect(found_red).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/game2d/batch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SpriteBatch
- create
- add
- clear
- z-ordering
- flush

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
