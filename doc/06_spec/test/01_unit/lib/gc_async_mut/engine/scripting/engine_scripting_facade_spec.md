# Engine Scripting Facade Specification

> 1. var graph = VisualGraph new

<!-- sdn-diagram:id=engine_scripting_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine_scripting_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine_scripting_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine_scripting_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Scripting Facade Specification

## Scenarios

### gc_async_mut engine scripting facade

#### re-exports visual graph node and connection helpers

1. var graph = VisualGraph new
   - Expected: graph.node_count() equals `2`
   - Expected: graph.connect(start, "exec", branch, "exec") is true
   - Expected: graph.connection_count() equals `1`
   - Expected: graph.get_connections_to(branch).length() equals `1`
   - Expected: graph.disconnect(start, branch) is true
   - Expected: graph.connection_count() equals `0`
2. var node = VisualNode new
3. node add input
4. node add output
   - Expected: node.input_count() equals `1`
   - Expected: node.output_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = VisualGraph.new("flow")
val start = graph.add_node("event", "Start")
val branch = graph.add_node("branch", "Branch")
expect(graph.node_count()).to_equal(2)
expect(graph.connect(start, "exec", branch, "exec")).to_equal(true)
expect(graph.connection_count()).to_equal(1)
expect(graph.get_connections_to(branch).length()).to_equal(1)
expect(graph.disconnect(start, branch)).to_equal(true)
expect(graph.connection_count()).to_equal(0)

var node = VisualNode.new(7, "custom", "Custom")
node.add_input("in", "float")
node.add_output("out", "float")
expect(node.input_count()).to_equal(1)
expect(node.output_count()).to_equal(1)
```

</details>

#### re-exports built-in node constructors

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = create_event_node(1, "Ready")
expect(event.output_count()).to_equal(1)
val branch = create_branch_node(2)
expect(branch.input_count()).to_equal(2)
val math = create_math_node(3, "add")
expect(math.output_count()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/engine/scripting/engine_scripting_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut engine scripting facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
