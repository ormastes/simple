# Scene Node Specification

> 1. check

<!-- sdn-diagram:id=scene_node_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scene_node_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scene_node_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scene_node_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scene Node Specification

## Scenarios

### SceneNode

#### creates nodes

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = SceneNode.new("test_node")
check(node.name == "test_node")
check(node.visible == true)
```

</details>

#### handles parent-child relationships

1. parent add child
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent = SceneNode.new("parent")
val child = SceneNode.new("child")
parent.add_child(child)
check(parent.get_children().len() == 1)
```

</details>

#### handles transforms

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = SceneNode.new("node_with_transform")
val transform = node.get_transform()
check(transform.x == 0.0)
check(transform.y == 0.0)
check(transform.z == 0.0)
```

</details>

#### handles visibility

1. check
2. node set visible
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = SceneNode.new("visible_node")
check(node.is_visible() == true)
node.set_visible(false)
check(node.is_visible() == false)
```

</details>

#### traverses scene graph

1. root add child
2. root add child
3. var children = root get children
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = SceneNode.new("root")
val child1 = SceneNode.new("child1")
val child2 = SceneNode.new("child2")
root.add_child(child1)
root.add_child(child2)
var children = root.get_children()
check(children.len() == 2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/game3d/scene_node_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SceneNode

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
