# Destruction Specification

> <details>

<!-- sdn-diagram:id=destruction_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=destruction_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

destruction_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=destruction_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Destruction Specification

## Scenarios

### Destructible

#### starts intact with full health

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dest = Destructible.new("wall", 100.0)
expect(dest.is_destroyed()).to_equal(false)
expect(dest.get_health()).to_equal(100.0)
expect(dest.fragment_count()).to_equal(0)
```

</details>

#### takes damage without destroying

1. var dest = Destructible new
   - Expected: destroyed is false
   - Expected: dest.get_health() equals `70.0`
   - Expected: dest.is_destroyed() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dest = Destructible.new("wall", 100.0)
val destroyed = dest.apply_damage(30.0)
expect(destroyed).to_equal(false)
expect(dest.get_health()).to_equal(70.0)
expect(dest.is_destroyed()).to_equal(false)
```

</details>

#### destroys when health reaches zero

1. var dest = Destructible new
2. dest add fragment
3. dest add fragment
   - Expected: destroyed is true
   - Expected: dest.is_destroyed() is true
   - Expected: dest.get_health() equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dest = Destructible.new("crate", 50.0)
dest.add_fragment(0.0, 0.0, 0.0, 1.0)
dest.add_fragment(1.0, 0.0, 0.0, 0.5)
val destroyed = dest.apply_damage(60.0)
expect(destroyed).to_equal(true)
expect(dest.is_destroyed()).to_equal(true)
expect(dest.get_health()).to_equal(0.0)
```

</details>

#### activates all fragments on destruction

1. var dest = Destructible new
2. dest add fragment
3. dest add fragment
4. dest add fragment
   - Expected: dest.active_fragment_count() equals `0`
5. dest apply damage
   - Expected: dest.active_fragment_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dest = Destructible.new("pot", 10.0)
dest.add_fragment(0.0, 0.0, 0.0, 1.0)
dest.add_fragment(1.0, 0.0, 0.0, 0.5)
dest.add_fragment(0.0, 1.0, 0.0, 0.5)
expect(dest.active_fragment_count()).to_equal(0)
dest.apply_damage(20.0)
expect(dest.active_fragment_count()).to_equal(3)
```

</details>

#### applies impulse to fragment

1. var dest = Destructible new
2. dest apply damage
3. dest apply impulse
4. dest update


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dest = Destructible.new("box", 10.0)
val fid = dest.add_fragment(0.0, 0.0, 0.0, 1.0)
dest.apply_damage(20.0)
dest.apply_impulse(fid, 5.0, 10.0, 0.0)
dest.update(1.0)
# Fragment should have moved by velocity * dt
```

</details>

#### updates fragment positions over time

1. var dest = Destructible new
2. dest add fragment
3. dest apply damage
4. dest apply impulse
5. dest update


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dest = Destructible.new("vase", 10.0)
dest.add_fragment(0.0, 0.0, 0.0, 1.0)
dest.apply_damage(20.0)
dest.apply_impulse(1, 2.0, 0.0, 0.0)
dest.update(0.5)
# Fragment moved 2.0 * 0.5 = 1.0 in x
```

</details>

#### does not update fragments before destruction

1. var dest = Destructible new
2. dest add fragment
3. dest apply impulse
4. dest update


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dest = Destructible.new("shelf", 100.0)
dest.add_fragment(0.0, 0.0, 0.0, 1.0)
dest.apply_impulse(1, 10.0, 0.0, 0.0)
dest.update(1.0)
# Not destroyed, so no movement
```

</details>

#### tracks fragment count

1. var dest = Destructible new
2. dest add fragment
3. dest add fragment
4. dest add fragment
5. dest add fragment
   - Expected: dest.fragment_count() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dest = Destructible.new("column", 200.0)
dest.add_fragment(0.0, 0.0, 0.0, 2.0)
dest.add_fragment(0.0, 1.0, 0.0, 1.0)
dest.add_fragment(0.0, 2.0, 0.0, 1.0)
dest.add_fragment(0.0, 3.0, 0.0, 0.5)
expect(dest.fragment_count()).to_equal(4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/destruction_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Destructible

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
