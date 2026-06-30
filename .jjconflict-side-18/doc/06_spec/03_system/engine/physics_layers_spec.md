# Physics Layers Specification

> <details>

<!-- sdn-diagram:id=physics_layers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=physics_layers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

physics_layers_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=physics_layers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Physics Layers Specification

## Scenarios

### Physics2 CollisionFilter

#### all vs all collides

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = CollisionFilter.all()
val b = CollisionFilter.all()
expect(a.should_collide(b)).to_equal(true)
```

</details>

#### none vs any no collision

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = CollisionFilter.none()
val a = CollisionFilter.all()
expect(n.should_collide(a)).to_equal(false)
```

</details>

#### same layer collides

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = CollisionFilter.with_mask(2, 2)
val y = CollisionFilter.with_mask(2, 2)
expect(x.should_collide(y)).to_equal(true)
```

</details>

#### different exclusive layers no collision

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = CollisionFilter.with_mask(2, 4)
val y = CollisionFilter.with_mask(8, 1)
expect(x.should_collide(y)).to_equal(false)
```

</details>

### Physics2 CollisionMatrix

<details>
<summary>Advanced: matrix disables collision between layers</summary>

#### matrix disables collision between layers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mx = matrix_with_disabled_24()
val fa = CollisionFilter.with_mask(2, 4)
val fb = CollisionFilter.with_mask(4, 2)
expect(mx.should_collide(fa, fb)).to_equal(false)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/physics_layers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Physics2 CollisionFilter
- Physics2 CollisionMatrix

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
