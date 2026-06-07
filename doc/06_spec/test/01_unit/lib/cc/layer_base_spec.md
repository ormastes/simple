# Layer Base Specification

> <details>

<!-- sdn-diagram:id=layer_base_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=layer_base_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

layer_base_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=layer_base_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layer Base Specification

## Scenarios

### cc::Layer base

#### layer_new: default opacity 1.0, is_drawable true, contents_opaque false

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = _make_layer(1)
expect(l.opacity).to_equal(1.0)
expect(l.is_drawable).to_equal(true)
expect(l.contents_opaque).to_equal(false)
```

</details>

#### layer_new: all tree indices are -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = _make_layer(2)
expect(l.transform_tree_index).to_equal(-1)
expect(l.clip_tree_index).to_equal(-1)
expect(l.effect_tree_index).to_equal(-1)
expect(l.scroll_tree_index).to_equal(-1)
```

</details>

#### is_root: parent_id -1 returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = _make_layer(3)
expect(l.is_root()).to_equal(true)
```

</details>

#### set_opacity: clamped to [0, 1]

1. l set opacity
   - Expected: l.opacity equals `1.0`
2. l set opacity
   - Expected: l.opacity equals `0.0`
3. l set opacity
   - Expected: l.opacity equals `0.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = _make_layer(4)
l.set_opacity(2.5)
expect(l.opacity).to_equal(1.0)
l.set_opacity(-0.3)
expect(l.opacity).to_equal(0.0)
l.set_opacity(0.5)
expect(l.opacity).to_equal(0.5)
```

</details>

#### set_bounds: updates bounds field

1. l set bounds
   - Expected: l.bounds.left equals `10.0`
   - Expected: l.bounds.top equals `20.0`
   - Expected: l.bounds.right equals `110.0`
   - Expected: l.bounds.bottom equals `120.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = _make_layer(5)
l.set_bounds(sk_rect(10.0, 20.0, 110.0, 120.0))
expect(l.bounds.left).to_equal(10.0)
expect(l.bounds.top).to_equal(20.0)
expect(l.bounds.right).to_equal(110.0)
expect(l.bounds.bottom).to_equal(120.0)
```

</details>

#### add_child: appends to children_ids

1. l add child
2. l add child
   - Expected: l.child_count() equals `2`
   - Expected: l.children_ids[0] equals `100`
   - Expected: l.children_ids[1] equals `101`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = _make_layer(6)
l.add_child(100)
l.add_child(101)
expect(l.child_count()).to_equal(2)
expect(l.children_ids[0]).to_equal(100)
expect(l.children_ids[1]).to_equal(101)
```

</details>

#### remove_child: removes existing child, returns true

1. l add child
2. l add child
3. l add child
   - Expected: ok is true
   - Expected: l.child_count() equals `2`
   - Expected: l.children_ids[0] equals `200`
   - Expected: l.children_ids[1] equals `202`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = _make_layer(7)
l.add_child(200)
l.add_child(201)
l.add_child(202)
val ok = l.remove_child(201)
expect(ok).to_equal(true)
expect(l.child_count()).to_equal(2)
expect(l.children_ids[0]).to_equal(200)
expect(l.children_ids[1]).to_equal(202)
```

</details>

#### remove_child: missing child returns false

1. l add child
   - Expected: ok is false
   - Expected: l.child_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = _make_layer(8)
l.add_child(300)
val ok = l.remove_child(999)
expect(ok).to_equal(false)
expect(l.child_count()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/cc/layer_base_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- cc::Layer base

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
