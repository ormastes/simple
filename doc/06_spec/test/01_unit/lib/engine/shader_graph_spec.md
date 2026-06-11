# Shader Graph Specification

> <details>

<!-- sdn-diagram:id=shader_graph_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shader_graph_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shader_graph_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shader_graph_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shader Graph Specification

## Scenarios

### ShaderNode

#### creates node with id and type

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = ShaderNode.new(0, "color", "base_color")
expect(node.id).to_equal(0)
expect(node.node_type).to_equal("color")
expect(node.name).to_equal("base_color")
expect(node.input_count()).to_equal(0)
expect(node.output_count()).to_equal(0)
```

</details>

#### adds inputs and outputs

1. var node = ShaderNode new
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
var node = ShaderNode.new(1, "multiply", "mul")
node.add_input("a", "float")
node.add_input("b", "float")
node.add_output("result", "float")
expect(node.input_count()).to_equal(2)
expect(node.output_count()).to_equal(1)
```

</details>

#### adds parameters

1. var node = ShaderNode new
2. node add parameter
3. node add parameter
4. node add parameter
   - Expected: node.parameters.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = ShaderNode.new(2, "color", "tint")
node.add_parameter("1.0")
node.add_parameter("0.5")
node.add_parameter("0.0")
expect(node.parameters.len()).to_equal(3)
```

</details>

### ShaderGraph

#### creates empty graph

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = ShaderGraph.new("test_material")
expect(graph.node_count()).to_equal(0)
expect(graph.connection_count()).to_equal(0)
```

</details>

#### adds nodes with auto-incrementing ids

1. var graph = ShaderGraph new
   - Expected: id0 equals `0`
   - Expected: id1 equals `1`
   - Expected: graph.node_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = ShaderGraph.new("mat")
val id0 = graph.add_node("color", "base")
val id1 = graph.add_node("output", "out")
expect(id0).to_equal(0)
expect(id1).to_equal(1)
expect(graph.node_count()).to_equal(2)
```

</details>

#### creates default ports for color node

1. var graph = ShaderGraph new
   - Expected: node.output_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = ShaderGraph.new("mat")
val id = graph.add_node("color", "base")
if val Some(node) = graph.get_node(id):
    expect(node.output_count()).to_equal(1)
```

</details>

#### creates default ports for output node

1. var graph = ShaderGraph new
   - Expected: node.input_count() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = ShaderGraph.new("mat")
val id = graph.add_node("output", "surface")
if val Some(node) = graph.get_node(id):
    expect(node.input_count()).to_equal(4)
```

</details>

#### connects nodes

1. var graph = ShaderGraph new
   - Expected: ok is true
   - Expected: graph.connection_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = ShaderGraph.new("mat")
val c_id = graph.add_node("color", "base")
val o_id = graph.add_node("output", "out")
val ok = graph.connect(c_id, "color", o_id, "albedo")
expect(ok).to_equal(true)
expect(graph.connection_count()).to_equal(1)
```

</details>

#### rejects connection to non-existent node

1. var graph = ShaderGraph new
2. graph add node
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = ShaderGraph.new("mat")
graph.add_node("color", "base")
val ok = graph.connect(0, "color", 99, "albedo")
expect(ok).to_equal(false)
```

</details>

#### disconnects nodes

1. var graph = ShaderGraph new
2. graph connect
   - Expected: graph.connection_count() equals `1`
   - Expected: ok is true
   - Expected: graph.connection_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = ShaderGraph.new("mat")
val c_id = graph.add_node("color", "base")
val o_id = graph.add_node("output", "out")
graph.connect(c_id, "color", o_id, "albedo")
expect(graph.connection_count()).to_equal(1)
val ok = graph.disconnect(c_id, "color", o_id, "albedo")
expect(ok).to_equal(true)
expect(graph.connection_count()).to_equal(0)
```

</details>

#### returns false when disconnecting non-existent connection

1. var graph = ShaderGraph new
2. graph add node
3. graph add node
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = ShaderGraph.new("mat")
graph.add_node("color", "base")
graph.add_node("output", "out")
val ok = graph.disconnect(0, "x", 1, "y")
expect(ok).to_equal(false)
```

</details>

#### gets node by id

1. var graph = ShaderGraph new
2. graph add node
   - Expected: node.name equals `tint`
   - Expected: node.node_type equals `color`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = ShaderGraph.new("mat")
graph.add_node("color", "tint")
if val Some(node) = graph.get_node(0):
    expect(node.name).to_equal("tint")
    expect(node.node_type).to_equal("color")
```

</details>

#### returns None for missing node

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = ShaderGraph.new("mat")
val maybe = graph.get_node(42)
# Should be None — no assertion needed, just verify no crash
```

</details>

#### gets connections to a node

1. var graph = ShaderGraph new
2. graph connect
3. graph connect
   - Expected: conns.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = ShaderGraph.new("mat")
val c_id = graph.add_node("color", "base")
val m_id = graph.add_node("multiply", "mul")
val o_id = graph.add_node("output", "out")
graph.connect(c_id, "color", o_id, "albedo")
graph.connect(m_id, "result", o_id, "roughness")
val conns = graph.get_connections_to(o_id)
expect(conns.len()).to_equal(2)
```

</details>

#### validates graph with valid connections

1. var graph = ShaderGraph new
2. graph connect
   - Expected: graph.validate() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = ShaderGraph.new("mat")
val c_id = graph.add_node("color", "base")
val o_id = graph.add_node("output", "out")
graph.connect(c_id, "color", o_id, "albedo")
expect(graph.validate()).to_equal(true)
```

</details>

#### validates empty graph

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = ShaderGraph.new("empty")
expect(graph.validate()).to_equal(true)
```

</details>

#### clears graph

1. var graph = ShaderGraph new
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
var graph = ShaderGraph.new("mat")
graph.add_node("color", "base")
graph.add_node("output", "out")
graph.connect(0, "color", 1, "albedo")
graph.clear()
expect(graph.node_count()).to_equal(0)
expect(graph.connection_count()).to_equal(0)
```

</details>

#### builds multi-node PBR graph

1. var graph = ShaderGraph new
2. graph connect
3. graph connect
4. graph connect
5. graph connect
6. graph connect
   - Expected: graph.node_count() equals `6`
   - Expected: graph.connection_count() equals `5`
   - Expected: graph.validate() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = ShaderGraph.new("pbr")
val albedo = graph.add_node("color", "albedo")
val tex = graph.add_node("texture_sample", "diffuse_tex")
val mix_id = graph.add_node("mix", "blend")
val nmap = graph.add_node("normal_map", "normals")
val fres = graph.add_node("fresnel", "rim")
val out = graph.add_node("output", "surface")
graph.connect(albedo, "color", mix_id, "a")
graph.connect(tex, "color", mix_id, "b")
graph.connect(mix_id, "result", out, "albedo")
graph.connect(nmap, "normal", out, "normal")
graph.connect(fres, "factor", out, "roughness")
expect(graph.node_count()).to_equal(6)
expect(graph.connection_count()).to_equal(5)
expect(graph.validate()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/shader_graph_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ShaderNode
- ShaderGraph

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
