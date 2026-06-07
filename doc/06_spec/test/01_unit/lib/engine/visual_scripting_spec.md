# Visual Scripting Specification

> 1. var graph = VisualGraph new

<!-- sdn-diagram:id=visual_scripting_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=visual_scripting_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

visual_scripting_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=visual_scripting_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Visual Scripting Specification

## Scenarios

### VisualGraph

#### adds nodes with auto-incrementing IDs

1. var graph = VisualGraph new
   - Expected: n1 equals `1`
   - Expected: n2 equals `2`
   - Expected: graph.node_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = VisualGraph.new("test_graph")
val n1 = graph.add_node("event", "OnStart")
val n2 = graph.add_node("print", "Log")
expect(n1).to_equal(1)
expect(n2).to_equal(2)
expect(graph.node_count()).to_equal(2)
```

</details>

#### connects and disconnects nodes

1. var graph = VisualGraph new
2. graph connect
   - Expected: graph.connection_count() equals `1`
3. graph disconnect
   - Expected: graph.connection_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = VisualGraph.new("test")
val n1 = graph.add_node("event", "OnStart")
val n2 = graph.add_node("print", "Log")
graph.connect(n1, "exec", n2, "exec")
expect(graph.connection_count()).to_equal(1)
graph.disconnect(n1, n2)
expect(graph.connection_count()).to_equal(0)
```

</details>

#### finds connections to a node

1. var graph = VisualGraph new
2. graph connect
3. graph connect
   - Expected: conns.len().to_i32() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = VisualGraph.new("test")
val n1 = graph.add_node("event", "A")
val n2 = graph.add_node("event", "B")
val n3 = graph.add_node("print", "C")
graph.connect(n1, "exec", n3, "exec")
graph.connect(n2, "exec", n3, "exec2")
val conns = graph.get_connections_to(n3)
expect(conns.len().to_i32()).to_equal(2)
```

</details>

#### clears all nodes and connections

1. var graph = VisualGraph new
2. graph add node
3. graph add node
4. graph connect
5. graph clear
   - Expected: graph.node_count() equals `0`
   - Expected: graph.connection_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = VisualGraph.new("test")
graph.add_node("event", "A")
graph.add_node("print", "B")
graph.connect(1, "exec", 2, "exec")
graph.clear()
expect(graph.node_count()).to_equal(0)
expect(graph.connection_count()).to_equal(0)
```

</details>

### VisualNode

#### manages input and output ports

1. var node = VisualNode new
2. node add input
3. node add input
4. node add output
   - Expected: node.input_count() equals `2`
   - Expected: node.output_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = VisualNode.new(1, "math", "Add")
node.add_input("a", "float")
node.add_input("b", "float")
node.add_output("result", "float")
expect(node.input_count()).to_equal(2)
expect(node.output_count()).to_equal(1)
```

</details>

### Node type factories

#### creates event node with exec output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = create_event_node(1, "OnStart")
expect(node.output_count()).to_equal(1)
expect(node.input_count()).to_equal(0)
```

</details>

#### creates branch node with condition input and two exec outputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = create_branch_node(2)
expect(node.input_count()).to_equal(2)
expect(node.output_count()).to_equal(2)
```

</details>

#### creates math node with two inputs and one output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = create_math_node(3, "add")
expect(node.input_count()).to_equal(2)
expect(node.output_count()).to_equal(1)
```

</details>

#### creates print node with exec flow

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = create_print_node(4)
expect(node.input_count()).to_equal(2)
expect(node.output_count()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/visual_scripting_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- VisualGraph
- VisualNode
- Node type factories

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
