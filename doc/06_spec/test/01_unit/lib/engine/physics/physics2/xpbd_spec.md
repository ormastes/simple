# Xpbd Specification

> <details>

<!-- sdn-diagram:id=xpbd_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=xpbd_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

xpbd_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=xpbd_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Xpbd Specification

## Scenarios

### XpbdWorld

#### creates empty world

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val world = XpbdWorld.create(4)
expect(world.particle_count).to_equal(0)
```

</details>

#### adds particles

1. var world = XpbdWorld create
   - Expected: world.particle_count equals `2`
   - Expected: a equals `0`
   - Expected: b equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = XpbdWorld.create(4)
val a = world.add_particle(0.0, 0.0, 0.0, 1.0)
val b = world.add_particle(1.0, 0.0, 0.0, 1.0)
expect(world.particle_count).to_equal(2)
expect(a).to_equal(0)
expect(b).to_equal(1)
```

</details>

#### fixed particle does not move

1. var world = XpbdWorld create
2. world step
   - Expected: pos.0 equals `5.0`
   - Expected: pos.1 equals `5.0`
   - Expected: pos.2 equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = XpbdWorld.create(4)
val fixed = world.add_fixed_particle(5.0, 5.0, 5.0)
world.step(0.016)
val pos = world.get_position(fixed)
expect(pos.0).to_equal(5.0)
expect(pos.1).to_equal(5.0)
expect(pos.2).to_equal(5.0)
```

</details>

#### free particle falls under gravity

1. var world = XpbdWorld create
2. world step
   - Expected: pos.1 < 10.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = XpbdWorld.create(4)
val p = world.add_particle(0.0, 10.0, 0.0, 1.0)
world.step(0.1)
val pos = world.get_position(p)
expect(pos.1 < 10.0).to_equal(true)
```

</details>

#### distance constraint maintains rest length

1. var world = XpbdWorld create
2. world add distance constraint
3. world step
   - Expected: dx < 3.0 is true
   - Expected: dx > 1.5 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = XpbdWorld.create(8)
world.gravity_y = 0.0
val a = world.add_particle(0.0, 0.0, 0.0, 1.0)
val b = world.add_particle(2.0, 0.0, 0.0, 1.0)
world.add_distance_constraint(a, b, 1000.0)
# Pull particle b away
var pb = world.particles[b]
pb.pos_x = 3.0
world.particles[b] = pb
world.step(0.016)
val pos_b = world.get_position(b)
val dx = pos_b.0 - 0.0
# Should pull back toward rest length of 2.0
expect(dx < 3.0).to_equal(true)
expect(dx > 1.5).to_equal(true)
```

</details>

#### cloth-like chain hangs under gravity

1. var world = XpbdWorld create
2. world add distance constraint
3. world add distance constraint
4. world add distance constraint
5. world step
6. world step
7. world step
8. world step
   - Expected: pos3.1 < 10.0 is true
   - Expected: pos0.1 equals `10.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = XpbdWorld.create(4)
val p0 = world.add_fixed_particle(0.0, 10.0, 0.0)
val p1 = world.add_particle(1.0, 10.0, 0.0, 1.0)
val p2 = world.add_particle(2.0, 10.0, 0.0, 1.0)
val p3 = world.add_particle(3.0, 10.0, 0.0, 1.0)
world.add_distance_constraint(p0, p1, 50.0)
world.add_distance_constraint(p1, p2, 50.0)
world.add_distance_constraint(p2, p3, 50.0)
world.step(0.5)
world.step(0.5)
world.step(0.5)
world.step(0.5)
val pos3 = world.get_position(p3)
# End particle should hang below start height
expect(pos3.1 < 10.0).to_equal(true)
# Fixed particle stays
val pos0 = world.get_position(p0)
expect(pos0.1).to_equal(10.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/physics/physics2/xpbd_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- XpbdWorld

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
