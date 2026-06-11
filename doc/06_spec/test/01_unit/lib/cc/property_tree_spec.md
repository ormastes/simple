# Property Tree Specification

> <details>

<!-- sdn-diagram:id=property_tree_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=property_tree_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

property_tree_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=property_tree_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Property Tree Specification

## Scenarios

### PropertyTrees

#### property_trees_new: has 1 root node of each kind (transform, clip, effect, scroll)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = property_trees_new()
expect(pt.transform_nodes.len().to_i64()).to_equal(1)
expect(pt.clip_nodes.len().to_i64()).to_equal(1)
expect(pt.effect_nodes.len().to_i64()).to_equal(1)
expect(pt.scroll_nodes.len().to_i64()).to_equal(1)
```

</details>

#### add_transform: returns index 1 after root (which is 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = property_trees_new()
val idx = pt.add_transform(Matrix3x3.identity(), 0)
expect(idx).to_equal(1)
```

</details>

#### compute_transform_to_root: root node returns identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = property_trees_new()
val m = pt.compute_transform_to_root(0)
expect(_approx(m.m00, 1.0)).to_equal(true)
expect(_approx(m.m11, 1.0)).to_equal(true)
expect(_approx(m.m22, 1.0)).to_equal(true)
expect(_approx(m.m01, 0.0)).to_equal(true)
expect(_approx(m.m02, 0.0)).to_equal(true)
expect(_approx(m.m12, 0.0)).to_equal(true)
```

</details>

#### compute_transform_to_root: translate child returns translate * identity = translate

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = property_trees_new()
val child = pt.add_transform(Matrix3x3.translate(10.0, 20.0), 0)
val m = pt.compute_transform_to_root(child)
expect(_approx(m.m02, 10.0)).to_equal(true)
expect(_approx(m.m12, 20.0)).to_equal(true)
expect(_approx(m.m00, 1.0)).to_equal(true)
expect(_approx(m.m11, 1.0)).to_equal(true)
```

</details>

#### compute_clip_to_root: inherits parent clip tighter than child

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = property_trees_new()
val parent = pt.add_clip(sk_rect(0.0, 0.0, 100.0, 100.0), 0)
val child = pt.add_clip(sk_rect(-50.0, -50.0, 200.0, 200.0), parent)
val r = pt.compute_clip_to_root(child)
# parent (0,0,100,100) tightens child (-50,-50,200,200) → (0,0,100,100)
expect(_approx(r.left, 0.0)).to_equal(true)
expect(_approx(r.top, 0.0)).to_equal(true)
expect(_approx(r.right, 100.0)).to_equal(true)
expect(_approx(r.bottom, 100.0)).to_equal(true)
```

</details>

#### compute_opacity_to_root: child with opacity 0.5 and parent 0.5 returns 0.25

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = property_trees_new()
val parent = pt.add_effect(0.5, 0, false)
val child = pt.add_effect(0.5, parent, false)
val op = pt.compute_opacity_to_root(child)
expect(_approx(op, 0.25)).to_equal(true)
```

</details>

#### compute_scroll_to_root: sums scroll offsets up chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = property_trees_new()
val parent = pt.add_scroll(10.0, 20.0, 0)
val child = pt.add_scroll(3.0, 4.0, parent)
val (sx, sy) = pt.compute_scroll_to_root(child)
expect(_approx(sx, 13.0)).to_equal(true)
expect(_approx(sy, 24.0)).to_equal(true)
```

</details>

#### add_effect: has_filter true is preserved

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = property_trees_new()
val idx = pt.add_effect(1.0, 0, true)
val opt = pt.effect_nodes.get(idx)
if val node = opt:
    expect(node.has_filter).to_equal(true)
else:
    fail("expected filtered child node")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/cc/property_tree_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PropertyTrees

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
