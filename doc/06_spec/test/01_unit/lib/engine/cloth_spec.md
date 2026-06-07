# Cloth Specification

> 1. var cloth = ClothSimulation new

<!-- sdn-diagram:id=cloth_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cloth_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cloth_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cloth_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cloth Specification

## Scenarios

### ClothSimulation

#### creates empty simulation

1. var cloth = ClothSimulation new
   - Expected: cloth.particle_count() equals `0`
   - Expected: cloth.constraint_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cloth = ClothSimulation.new(9.81, 0.99, 5)
expect(cloth.particle_count()).to_equal(0)
expect(cloth.constraint_count()).to_equal(0)
```

</details>

#### adds particles

1. var cloth = ClothSimulation new
   - Expected: cloth.particle_count() equals `2`
   - Expected: i0 equals `0`
   - Expected: i1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cloth = ClothSimulation.new(9.81, 0.99, 5)
val i0 = cloth.add_particle(0.0, 0.0, 1.0, true)
val i1 = cloth.add_particle(1.0, 0.0, 1.0, false)
expect(cloth.particle_count()).to_equal(2)
expect(i0).to_equal(0)
expect(i1).to_equal(1)
```

</details>

#### adds constraints with auto rest length

1. var cloth = ClothSimulation new
2. cloth add particle
3. cloth add particle
   - Expected: cloth.constraint_count() equals `1`
   - Expected: ci equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cloth = ClothSimulation.new(9.81, 0.99, 5)
cloth.add_particle(0.0, 0.0, 1.0, false)
cloth.add_particle(1.0, 0.0, 1.0, false)
val ci = cloth.add_constraint(0, 1)
expect(cloth.constraint_count()).to_equal(1)
expect(ci).to_equal(0)
```

</details>

#### pins and unpins particles

1. var cloth = ClothSimulation new
2. cloth add particle
3. cloth pin particle
   - Expected: p.pinned is true
4. cloth unpin particle
   - Expected: p2.pinned is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cloth = ClothSimulation.new(9.81, 0.99, 5)
cloth.add_particle(0.0, 0.0, 1.0, false)
cloth.pin_particle(0)
if val Some(p) = cloth.get_particle(0):
    expect(p.pinned).to_equal(true)
cloth.unpin_particle(0)
if val Some(p2) = cloth.get_particle(0):
    expect(p2.pinned).to_equal(false)
```

</details>

#### pinned particles stay fixed during simulation

1. var cloth = ClothSimulation new
2. cloth add particle
3. cloth add particle
4. cloth add constraint
5. cloth simulate
   - Expected: p.x equals `0.0`
   - Expected: p.y equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cloth = ClothSimulation.new(9.81, 0.99, 5)
cloth.add_particle(0.0, 0.0, 1.0, true)
cloth.add_particle(1.0, 0.0, 1.0, false)
cloth.add_constraint(0, 1)
cloth.simulate(0.016)
if val Some(p) = cloth.get_particle(0):
    expect(p.x).to_equal(0.0)
    expect(p.y).to_equal(0.0)
```

</details>

#### unpinned particles move under gravity

1. var cloth = ClothSimulation new
2. cloth add particle
3. cloth simulate


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cloth = ClothSimulation.new(9.81, 0.99, 5)
cloth.add_particle(0.0, 0.0, 1.0, false)
cloth.simulate(0.1)
if val Some(p) = cloth.get_particle(0):
    expect(p.y).to_be_greater_than(0.0)
```

</details>

#### retrieves particle by index

1. var cloth = ClothSimulation new
2. cloth add particle
   - Expected: p.x equals `3.0`
   - Expected: p.y equals `4.0`
   - Expected: p.mass equals `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cloth = ClothSimulation.new(9.81, 0.99, 5)
cloth.add_particle(3.0, 4.0, 2.0, false)
if val Some(p) = cloth.get_particle(0):
    expect(p.x).to_equal(3.0)
    expect(p.y).to_equal(4.0)
    expect(p.mass).to_equal(2.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/cloth_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ClothSimulation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
