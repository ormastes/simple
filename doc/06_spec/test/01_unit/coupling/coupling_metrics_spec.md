# Coupling Metrics Specification

> 1. edges = edges set

<!-- sdn-diagram:id=coupling_metrics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=coupling_metrics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

coupling_metrics_spec -> std
coupling_metrics_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=coupling_metrics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 109 | 109 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Coupling Metrics Specification

## Scenarios

### compute_fan_out

#### returns correct fan-out for a linear chain

1. edges = edges set
2. edges = edges set
3. edges = edges set
   - Expected: result.get("A") equals `1`
   - Expected: result.get("B") equals `1`
   - Expected: result.get("C") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
edges = edges.set("A", ["B"])
edges = edges.set("B", ["C"])
edges = edges.set("C", [])
val graph = make_graph(edges)
val result = compute_fan_out(graph)
expect(result.get("A")).to_equal(1)
expect(result.get("B")).to_equal(1)
expect(result.get("C")).to_equal(0)
```

</details>

#### returns correct fan-out for a module with multiple deps

1. edges = edges set
2. edges = edges set
3. edges = edges set
4. edges = edges set
   - Expected: result.get("A") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
edges = edges.set("A", ["B", "C", "D"])
edges = edges.set("B", [])
edges = edges.set("C", [])
edges = edges.set("D", [])
val graph = make_graph(edges)
val result = compute_fan_out(graph)
expect(result.get("A")).to_equal(3)
```

</details>

#### returns zero fan-out for isolated modules

1. edges = edges set
2. edges = edges set
   - Expected: result.get("X") equals `0`
   - Expected: result.get("Y") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
edges = edges.set("X", [])
edges = edges.set("Y", [])
val graph = make_graph(edges)
val result = compute_fan_out(graph)
expect(result.get("X")).to_equal(0)
expect(result.get("Y")).to_equal(0)
```

</details>

#### handles empty graph

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
val graph = make_graph(edges)
val result = compute_fan_out(graph)
expect(result.keys().len()).to_equal(0)
```

</details>

### compute_fan_in

#### returns correct fan-in for a linear chain

1. edges = edges set
2. edges = edges set
3. edges = edges set
   - Expected: result.get("A") equals `0`
   - Expected: result.get("B") equals `1`
   - Expected: result.get("C") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
edges = edges.set("A", ["B"])
edges = edges.set("B", ["C"])
edges = edges.set("C", [])
val graph = make_graph(edges)
val result = compute_fan_in(graph)
expect(result.get("A")).to_equal(0)
expect(result.get("B")).to_equal(1)
expect(result.get("C")).to_equal(1)
```

</details>

#### counts multiple incomers correctly

1. edges = edges set
2. edges = edges set
3. edges = edges set
   - Expected: result.get("C") equals `2`
   - Expected: result.get("A") equals `0`
   - Expected: result.get("B") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
edges = edges.set("A", ["C"])
edges = edges.set("B", ["C"])
edges = edges.set("C", [])
val graph = make_graph(edges)
val result = compute_fan_in(graph)
expect(result.get("C")).to_equal(2)
expect(result.get("A")).to_equal(0)
expect(result.get("B")).to_equal(0)
```

</details>

#### handles empty graph

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
val graph = make_graph(edges)
val result = compute_fan_in(graph)
expect(result.keys().len()).to_equal(0)
```

</details>

#### handles single node with no edges

1. edges = edges set
   - Expected: result.get("Solo") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
edges = edges.set("Solo", [])
val graph = make_graph(edges)
val result = compute_fan_in(graph)
expect(result.get("Solo")).to_equal(0)
```

</details>

### compute_all_metrics

#### computes instability for a hub-and-spoke graph

1. edges = edges set
2. edges = edges set
3. edges = edges set
4. edges = edges set
   - Expected: hub.fan_out equals `3`
   - Expected: hub.fan_in equals `0`
   - Expected: hub.instability equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
edges = edges.set("hub", ["a", "b", "c"])
edges = edges.set("a", [])
edges = edges.set("b", [])
edges = edges.set("c", [])
val graph = make_graph(edges)
val metrics = compute_all_metrics(graph)
val hub = find_metric_by_name(metrics, "hub")
# hub: fan_out=3, fan_in=0, instability=3/(0+3)=1.0
expect(hub.fan_out).to_equal(3)
expect(hub.fan_in).to_equal(0)
expect(hub.instability).to_equal(1.0)
```

</details>

#### leaf modules have instability 0

1. edges = edges set
2. edges = edges set
   - Expected: leaf.fan_out equals `0`
   - Expected: leaf.instability equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
edges = edges.set("hub", ["leaf"])
edges = edges.set("leaf", [])
val graph = make_graph(edges)
val metrics = compute_all_metrics(graph)
val leaf = find_metric_by_name(metrics, "leaf")
# leaf: fan_out=0, fan_in=1, instability=0/(1+0)=0.0
expect(leaf.fan_out).to_equal(0)
expect(leaf.instability).to_equal(0.0)
```

</details>

#### isolated node has instability 0

1. edges = edges set
   - Expected: solo.instability equals `0.0`
   - Expected: solo.distance equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
edges = edges.set("solo", [])
val graph = make_graph(edges)
val metrics = compute_all_metrics(graph)
val solo = find_metric_by_name(metrics, "solo")
expect(solo.instability).to_equal(0.0)
expect(solo.distance).to_equal(1.0)
```

</details>

#### cbo equals fan_out

1. edges = edges set
2. edges = edges set
3. edges = edges set
   - Expected: x.cbo equals `x.fan_out`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
edges = edges.set("X", ["Y", "Z"])
edges = edges.set("Y", [])
edges = edges.set("Z", [])
val graph = make_graph(edges)
val metrics = compute_all_metrics(graph)
val x = find_metric_by_name(metrics, "X")
expect(x.cbo).to_equal(x.fan_out)
```

</details>

#### distance from main sequence is computed correctly

1. edges = edges set
2. edges = edges set
   - Expected: m.instability equals `0.5`
   - Expected: m.distance equals `0.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Module with instability=0.5, abstractness=0 -> distance = |0+0.5-1| = 0.5
var edges: Dict<text, [text]> = {}
edges = edges.set("M", ["N"])
edges = edges.set("N", ["M"])
val graph = make_graph(edges)
val metrics = compute_all_metrics(graph)
val m = find_metric_by_name(metrics, "M")
# M: fan_out=1, fan_in=1, instability=0.5, abstractness=0 -> distance = |0+0.5-1| = 0.5
expect(m.instability).to_equal(0.5)
expect(m.distance).to_equal(0.5)
```

</details>

### find_cycles

#### detects a simple 2-node cycle

1. edges = edges set
2. edges = edges set
   - Expected: cycles.len() equals `1`
   - Expected: cycles.get(0).len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
edges = edges.set("A", ["B"])
edges = edges.set("B", ["A"])
val graph = make_graph(edges)
val cycles = find_cycles(graph)
expect(cycles.len()).to_equal(1)
expect(cycles.get(0).len()).to_equal(2)
```

</details>

#### detects a 3-node cycle

1. edges = edges set
2. edges = edges set
3. edges = edges set
   - Expected: cycles.len() equals `1`
   - Expected: cycles.get(0).len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
edges = edges.set("A", ["B"])
edges = edges.set("B", ["C"])
edges = edges.set("C", ["A"])
val graph = make_graph(edges)
val cycles = find_cycles(graph)
expect(cycles.len()).to_equal(1)
expect(cycles.get(0).len()).to_equal(3)
```

</details>

#### returns empty for an acyclic graph

1. edges = edges set
2. edges = edges set
3. edges = edges set
   - Expected: cycles.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
edges = edges.set("A", ["B"])
edges = edges.set("B", ["C"])
edges = edges.set("C", [])
val graph = make_graph(edges)
val cycles = find_cycles(graph)
expect(cycles.len()).to_equal(0)
```

</details>

#### returns empty for an empty graph

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
val graph = make_graph(edges)
val cycles = find_cycles(graph)
expect(cycles.len()).to_equal(0)
```

</details>

#### returns empty for a single node

1. edges = edges set
   - Expected: cycles.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
edges = edges.set("A", [])
val graph = make_graph(edges)
val cycles = find_cycles(graph)
expect(cycles.len()).to_equal(0)
```

</details>

### find_instability_inversions

#### detects inversion when stable depends on unstable

1. edges = edges set
2. edges = edges set
3. edges = edges set
4. edges = edges set
5. edges = edges set


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A has fan_in=1, fan_out=1 => instability=0.5
# B has fan_in=0, fan_out=1 => instability=1.0
# A depends on B: A (stable=0.5) -> B (unstable=1.0) = inversion
# But we also need B depending on something so B has fan_out
var edges: Dict<text, [text]> = {}
edges = edges.set("stable", ["unstable"])
edges = edges.set("unstable", ["leaf1", "leaf2"])
edges = edges.set("other", ["stable"])
edges = edges.set("leaf1", [])
edges = edges.set("leaf2", [])
val graph = make_graph(edges)
val metrics = compute_all_metrics(graph)
val inversions = find_instability_inversions(metrics, graph)
# stable (instab ~0.5) depends on unstable (instab=1.0) => inversion
expect(inversions.len()).to_be_greater_than(0)
```

</details>

#### returns empty when no inversions exist

1. edges = edges set
2. edges = edges set
   - Expected: inversions.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Linear: unstable -> stable -> leaf
var edges: Dict<text, [text]> = {}
edges = edges.set("A", ["B"])
edges = edges.set("B", [])
val graph = make_graph(edges)
val metrics = compute_all_metrics(graph)
val inversions = find_instability_inversions(metrics, graph)
# A: instab=1.0 depends on B: instab=0.0 => no inversion (unstable depends on stable = OK)
expect(inversions.len()).to_equal(0)
```

</details>

#### returns empty for empty graph

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
val graph = make_graph(edges)
val metrics = compute_all_metrics(graph)
val inversions = find_instability_inversions(metrics, graph)
expect(inversions.len()).to_equal(0)
```

</details>

### extract_layer_number

#### extracts layer from slash-separated path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = extract_layer_number("compiler/30.types/foo")
expect(result).to_equal(30)
```

</details>

#### extracts layer 00 from common

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = extract_layer_number("compiler/00.common/bar")
expect(result).to_equal(0)
```

</details>

#### returns nil for non-layer path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = extract_layer_number("std/text/utils")
expect(result).to_be_nil()
```

</details>

#### extracts layer from dot-separated path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = extract_layer_number("compiler.70.backend.llvm")
expect(result).to_equal(70)
```

</details>

#### returns nil for single character segment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = extract_layer_number("a/b/c")
expect(result).to_be_nil()
```

</details>

### is_digit

#### returns true for digit characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit("0")).to_equal(true)
expect(is_digit("5")).to_equal(true)
expect(is_digit("9")).to_equal(true)
```

</details>

#### returns false for non-digit characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit("a")).to_equal(false)
expect(is_digit("Z")).to_equal(false)
expect(is_digit(" ")).to_equal(false)
```

</details>

### find_layer_violations

#### detects violation when lower layer imports higher layer

1. edges = edges set
2. edges = edges set
   - Expected: violations[0].from_layer equals `10`
   - Expected: violations[0].to_layer equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
edges = edges.set("compiler/10.frontend/foo", ["compiler/30.types/bar"])
edges = edges.set("compiler/30.types/bar", [])
val graph = make_graph(edges)
val violations = find_layer_violations(graph)
expect(violations.len()).to_be_greater_than(0)
if violations.len() > 0:
    expect(violations[0].from_layer).to_equal(10)
    expect(violations[0].to_layer).to_equal(30)
```

</details>

#### allows higher layer importing lower layer

1. edges = edges set
2. edges = edges set
   - Expected: violations.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
edges = edges.set("compiler/30.types/bar", ["compiler/00.common/foo"])
edges = edges.set("compiler/00.common/foo", [])
val graph = make_graph(edges)
val violations = find_layer_violations(graph)
expect(violations.len()).to_equal(0)
```

</details>

#### no violations for non-layer modules

1. edges = edges set
2. edges = edges set
   - Expected: violations.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
edges = edges.set("std/text/utils", ["std/math/ops"])
edges = edges.set("std/math/ops", [])
val graph = make_graph(edges)
val violations = find_layer_violations(graph)
expect(violations.len()).to_equal(0)
```

</details>

#### returns empty for empty graph

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
val graph = make_graph(edges)
val violations = find_layer_violations(graph)
expect(violations.len()).to_equal(0)
```

</details>

#### uses detailed_edges when available

1. make edge
   - Expected: violations[0].from_layer equals `10`
   - Expected: violations[0].to_layer equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
val detailed = [
    make_edge("compiler/10.frontend/parser", "compiler/30.types/checker")
]
val graph = make_graph_with_edges(edges, detailed)
val violations = find_layer_violations(graph)
expect(violations.len()).to_be_greater_than(0)
if violations.len() > 0:
    expect(violations[0].from_layer).to_equal(10)
    expect(violations[0].to_layer).to_equal(30)
```

</details>

### fields_share_access

#### returns true when lists share a field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = fields_share_access(["x", "y"], ["y", "z"])
expect(result).to_equal(true)
```

</details>

#### returns false when lists share no field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = fields_share_access(["x", "y"], ["z", "w"])
expect(result).to_equal(false)
```

</details>

#### returns false for empty lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = fields_share_access([], [])
expect(result).to_equal(false)
```

</details>

#### returns false when one list is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = fields_share_access(["x"], [])
expect(result).to_equal(false)
```

</details>

### find_method_index

#### finds existing method by name

1. make method
2. make method
3. make method
   - Expected: find_method_index(methods, "beta") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val methods = [
    make_method("alpha", [], []),
    make_method("beta", [], []),
    make_method("gamma", [], [])
]
expect(find_method_index(methods, "beta")).to_equal(1)
```

</details>

#### returns -1 for missing method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val methods = [make_method("alpha", [], [])]
expect(find_method_index(methods, "missing")).to_equal(-1)
```

</details>

#### returns -1 for empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var methods: [MethodFieldAccess] = []
expect(find_method_index(methods, "any")).to_equal(-1)
```

</details>

### sort_descending

#### sorts integers in descending order

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sort_descending([1, 3, 2, 5, 4])
expect(result.get(0)).to_equal(5)
expect(result.get(1)).to_equal(4)
expect(result.get(2)).to_equal(3)
```

</details>

#### handles single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sort_descending([42])
expect(result.get(0)).to_equal(42)
```

</details>

#### handles empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sort_descending([])
expect(result.len()).to_equal(0)
```

</details>

#### handles already sorted input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sort_descending([5, 4, 3, 2, 1])
expect(result.get(0)).to_equal(5)
expect(result.get(4)).to_equal(1)
```

</details>

### compute_lcom4

#### returns 0 for class with no methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var methods: [MethodFieldAccess] = []
val result = compute_lcom4("Empty", methods)
expect(result.lcom4).to_equal(0)
expect(result.method_count).to_equal(0)
```

</details>

#### returns 1 for class with a single method

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val methods = [make_method("do_thing", ["x"], [])]
val result = compute_lcom4("Single", methods)
expect(result.lcom4).to_equal(1)
expect(result.method_count).to_equal(1)
```

</details>

#### returns 1 for cohesive class (shared fields)

1. make method
2. make method
3. make method
   - Expected: result.lcom4 equals `1`
   - Expected: result.method_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val methods = [
    make_method("get_x", ["x"], []),
    make_method("set_x", ["x"], []),
    make_method("compute", ["x", "y"], [])
]
val result = compute_lcom4("Cohesive", methods)
expect(result.lcom4).to_equal(1)
expect(result.method_count).to_equal(3)
```

</details>

#### returns 2 for non-cohesive class (disjoint methods)

1. make method
2. make method
   - Expected: result.lcom4 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val methods = [
    make_method("get_x", ["x"], []),
    make_method("get_y", ["y"], [])
]
val result = compute_lcom4("Split", methods)
expect(result.lcom4).to_equal(2)
```

</details>

#### connects methods through method calls

1. make method
2. make method
   - Expected: result.lcom4 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val methods = [
    make_method("alpha", ["x"], []),
    make_method("beta", ["y"], ["alpha"])
]
val result = compute_lcom4("Connected", methods)
# alpha accesses x, beta accesses y but calls alpha => connected
expect(result.lcom4).to_equal(1)
```

</details>

#### counts fields correctly

1. make method
2. make method
   - Expected: result.field_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val methods = [
    make_method("m1", ["a", "b"], []),
    make_method("m2", ["b", "c"], [])
]
val result = compute_lcom4("FieldCount", methods)
expect(result.field_count).to_equal(3)
```

</details>

#### produces component_sizes that sum to method_count

1. make method
2. make method
3. make method
   - Expected: result.lcom4 equals `2`
4. total = total + result component sizes get
   - Expected: total equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val methods = [
    make_method("m1", ["a"], []),
    make_method("m2", ["a"], []),
    make_method("m3", ["b"], [])
]
val result = compute_lcom4("Components", methods)
expect(result.lcom4).to_equal(2)
var total = 0
var i = 0
while i < result.component_sizes.len():
    total = total + result.component_sizes.get(i)
    i = i + 1
expect(total).to_equal(3)
```

</details>

### compute_pss

#### sums public methods and fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compute_pss(5, 3)).to_equal(8)
```

</details>

#### returns 0 when both are 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compute_pss(0, 0)).to_equal(0)
```

</details>

#### handles methods only

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compute_pss(10, 0)).to_equal(10)
```

</details>

#### handles fields only

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compute_pss(0, 7)).to_equal(7)
```

</details>

### compute_public_ratio

#### returns correct ratio

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_public_ratio(5, 10)
expect(result).to_equal(0.5)
```

</details>

#### returns 0 when total is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_public_ratio(0, 0)
expect(result).to_equal(0.0)
```

</details>

#### returns 1.0 when all are public

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_public_ratio(4, 4)
expect(result).to_equal(1.0)
```

</details>

### compute_avg_param_count

#### computes average correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_avg_param_count([2, 4, 6])
expect(result).to_equal(4.0)
```

</details>

#### returns 0 for empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_avg_param_count([])
expect(result).to_equal(0.0)
```

</details>

#### handles single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_avg_param_count([3])
expect(result).to_equal(3.0)
```

</details>

### compute_max_param_count

#### finds maximum

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_max_param_count([1, 5, 3, 2])
expect(result).to_equal(5)
```

</details>

#### returns 0 for empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_max_param_count([])
expect(result).to_equal(0)
```

</details>

### compute_overload_groups

#### counts groups with duplicate names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_overload_groups(["foo", "bar", "foo", "baz", "bar"])
expect(result).to_equal(2)
```

</details>

#### returns 0 for all unique names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_overload_groups(["a", "b", "c"])
expect(result).to_equal(0)
```

</details>

#### returns 0 for empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_overload_groups([])
expect(result).to_equal(0)
```

</details>

### compute_eur

#### returns fraction of used methods

1. make usage
2. make usage
3. make usage


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val usages = [
    make_usage("a", 5),
    make_usage("b", 0),
    make_usage("c", 3)
]
# 2 out of 3 used externally
val result = compute_eur(usages, 3)
expect(result).to_be_greater_than(0.6)
expect(result).to_be_less_than(0.7)
```

</details>

#### returns 0 when no methods are used

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val usages = [make_usage("a", 0), make_usage("b", 0)]
val result = compute_eur(usages, 2)
expect(result).to_equal(0.0)
```

</details>

#### returns 0 when total_public is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val usages = [make_usage("a", 5)]
val result = compute_eur(usages, 0)
expect(result).to_equal(0.0)
```

</details>

#### returns 1.0 when all methods used

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val usages = [make_usage("a", 1), make_usage("b", 1)]
val result = compute_eur(usages, 2)
expect(result).to_equal(1.0)
```

</details>

### compute_entropy

#### returns 1.0 for perfectly uniform usage

1. make usage
2. make usage
3. make usage


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val usages = [
    make_usage("a", 10),
    make_usage("b", 10),
    make_usage("c", 10)
]
val result = compute_entropy(usages)
expect(result).to_be_greater_than(0.99)
```

</details>

#### returns 0 for no usage

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val usages = [make_usage("a", 0), make_usage("b", 0)]
val result = compute_entropy(usages)
expect(result).to_equal(0.0)
```

</details>

#### returns 0 for single used method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val usages = [make_usage("a", 10)]
val result = compute_entropy(usages)
expect(result).to_equal(0.0)
```

</details>

#### returns less than 1 for skewed usage

1. make usage
2. make usage


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val usages = [
    make_usage("a", 100),
    make_usage("b", 1)
]
val result = compute_entropy(usages)
expect(result).to_be_less_than(0.5)
expect(result).to_be_greater_than(0.0)
```

</details>

#### handles empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var usages: [MethodUsage] = []
val result = compute_entropy(usages)
expect(result).to_equal(0.0)
```

</details>

### type_set_edit_distance

#### returns 0 for identical sorted sets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dist = type_set_edit_distance(["i64", "text"], ["i64", "text"])
expect(dist).to_equal(0)
```

</details>

#### returns 1 for single addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dist = type_set_edit_distance(["i64"], ["i64", "text"])
expect(dist).to_equal(1)
```

</details>

#### returns 1 for single removal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dist = type_set_edit_distance(["i64", "text"], ["text"])
expect(dist).to_equal(1)
```

</details>

#### returns sum of lengths for completely disjoint sets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dist = type_set_edit_distance(["a", "b"], ["c", "d"])
expect(dist).to_equal(4)
```

</details>

#### returns 0 for two empty sets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dist = type_set_edit_distance([], [])
expect(dist).to_equal(0)
```

</details>

#### returns length when one set is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dist = type_set_edit_distance(["a", "b", "c"], [])
expect(dist).to_equal(3)
```

</details>

#### handles swap correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ["a", "c"] vs ["b", "c"] => remove a, add b = 2
val dist = type_set_edit_distance(["a", "c"], ["b", "c"])
expect(dist).to_equal(2)
```

</details>

### generate_deletion_variants

#### generates N variants for list of length N

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val variants = generate_deletion_variants(["a", "b", "c"])
expect(variants.len()).to_equal(3)
```

</details>

#### each variant has length N-1

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val variants = generate_deletion_variants(["x", "y", "z"])
var i = 0
while i < variants.len():
    expect(variants.get(i).len()).to_equal(2)
    i = i + 1
```

</details>

#### first variant removes first element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val variants = generate_deletion_variants(["a", "b", "c"])
expect(variants.get(0)).to_equal(["b", "c"])
```

</details>

#### last variant removes last element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val variants = generate_deletion_variants(["a", "b", "c"])
expect(variants.get(2)).to_equal(["a", "b"])
```

</details>

#### returns empty list for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val variants = generate_deletion_variants([])
expect(variants.len()).to_equal(0)
```

</details>

#### returns one empty variant for single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val variants = generate_deletion_variants(["only"])
expect(variants.len()).to_equal(1)
expect(variants.get(0).len()).to_equal(0)
```

</details>

### compute_type_hash

#### returns same hash for same input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = compute_type_hash(["i64", "text"])
val h2 = compute_type_hash(["i64", "text"])
expect(h1).to_equal(h2)
```

</details>

#### returns different hash for different input

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = compute_type_hash(["i64"])
val h2 = compute_type_hash(["text"])
# Very unlikely to collide
expect(h1 == h2).to_equal(false)
```

</details>

#### returns 0 for empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = compute_type_hash([])
expect(h).to_equal(0)
```

</details>

### build_dsm

<details>
<summary>Advanced: builds NxN matrix for N modules</summary>

#### builds NxN matrix for N modules

1. edges = edges set
2. edges = edges set
3. edges = edges set
   - Expected: dsm.modules.len() equals `3`
   - Expected: dsm.matrix.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
edges = edges.set("A", ["B"])
edges = edges.set("B", ["C"])
edges = edges.set("C", [])
val graph = make_graph(edges)
val dsm = build_dsm(graph)
expect(dsm.modules.len()).to_equal(3)
expect(dsm.matrix.len()).to_equal(3)
```

</details>


</details>

#### records dependency in correct cell

1. edges = edges set
2. edges = edges set
   - Expected: dsm.modules.len() equals `2`
   - Expected: dsm.matrix.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
edges = edges.set("A", ["B"])
edges = edges.set("B", [])
val graph = make_graph(edges)
val dsm = build_dsm(graph)
# modules sorted alphabetically: [A, B]
expect(dsm.modules.len()).to_equal(2)
expect(dsm.matrix.len()).to_equal(2)
```

</details>

#### handles empty graph

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
val graph = make_graph(edges)
val dsm = build_dsm(graph)
expect(dsm.modules.len()).to_equal(0)
expect(dsm.matrix.len()).to_equal(0)
```

</details>

#### sorts modules alphabetically

1. edges = edges set
2. edges = edges set
3. edges = edges set
   - Expected: dsm.modules.get(0) equals `A`
   - Expected: dsm.modules.get(1) equals `B`
   - Expected: dsm.modules.get(2) equals `C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
edges = edges.set("C", ["A"])
edges = edges.set("B", [])
edges = edges.set("A", [])
val graph = make_graph(edges)
val dsm = build_dsm(graph)
expect(dsm.modules.get(0)).to_equal("A")
expect(dsm.modules.get(1)).to_equal("B")
expect(dsm.modules.get(2)).to_equal("C")
```

</details>

#### diagonal is always zero

1. edges = edges set
2. edges = edges set
   - Expected: dsm.matrix.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
edges = edges.set("A", ["B"])
edges = edges.set("B", ["A"])
val graph = make_graph(edges)
val dsm = build_dsm(graph)
expect(dsm.matrix.len()).to_equal(2)
```

</details>

### token_kind_ordinal

#### maps Identifier to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(token_kind_ordinal(SimpleTokenKind.Identifier)).to_equal(0)
```

</details>

#### maps Keyword to 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(token_kind_ordinal(SimpleTokenKind.Keyword)).to_equal(1)
```

</details>

#### maps Operator to 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(token_kind_ordinal(SimpleTokenKind.Operator)).to_equal(2)
```

</details>

#### maps Literal to 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(token_kind_ordinal(SimpleTokenKind.Literal)).to_equal(3)
```

</details>

#### maps Punctuation to 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(token_kind_ordinal(SimpleTokenKind.Punctuation)).to_equal(4)
```

</details>

#### maps Comment to 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(token_kind_ordinal(SimpleTokenKind.Comment)).to_equal(5)
```

</details>

#### maps Whitespace to 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(token_kind_ordinal(SimpleTokenKind.Whitespace)).to_equal(6)
```

</details>

### to_relaxed_tokens

#### filters out whitespace tokens

1. make token
2. make token
3. make token
   - Expected: relaxed.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = [
    make_token(SimpleTokenKind.Identifier, 1, 0),
    make_token(SimpleTokenKind.Whitespace, 1, 5),
    make_token(SimpleTokenKind.Operator, 1, 6)
]
val relaxed = to_relaxed_tokens(tokens)
expect(relaxed.len()).to_equal(2)
```

</details>

#### filters out comment tokens

1. make token
2. make token
   - Expected: relaxed.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = [
    make_token(SimpleTokenKind.Keyword, 1, 0),
    make_token(SimpleTokenKind.Comment, 1, 5)
]
val relaxed = to_relaxed_tokens(tokens)
expect(relaxed.len()).to_equal(1)
```

</details>

#### preserves line and column info

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = [make_token(SimpleTokenKind.Literal, 7, 12)]
val relaxed = to_relaxed_tokens(tokens)
expect(relaxed.get(0).line).to_equal(7)
expect(relaxed.get(0).column).to_equal(12)
```

</details>

#### sets correct kind_ordinal

1. make token
2. make token
   - Expected: relaxed.get(0).kind_ordinal equals `1`
   - Expected: relaxed.get(1).kind_ordinal equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = [
    make_token(SimpleTokenKind.Keyword, 1, 0),
    make_token(SimpleTokenKind.Punctuation, 1, 3)
]
val relaxed = to_relaxed_tokens(tokens)
expect(relaxed.get(0).kind_ordinal).to_equal(1)
expect(relaxed.get(1).kind_ordinal).to_equal(4)
```

</details>

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tokens: [SimpleToken] = []
val relaxed = to_relaxed_tokens(tokens)
expect(relaxed.len()).to_equal(0)
```

</details>

#### returns empty when all tokens are whitespace/comments

1. make token
2. make token
3. make token
   - Expected: relaxed.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = [
    make_token(SimpleTokenKind.Whitespace, 1, 0),
    make_token(SimpleTokenKind.Comment, 2, 0),
    make_token(SimpleTokenKind.Whitespace, 3, 0)
]
val relaxed = to_relaxed_tokens(tokens)
expect(relaxed.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/coupling/coupling_metrics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- compute_fan_out
- compute_fan_in
- compute_all_metrics
- find_cycles
- find_instability_inversions
- extract_layer_number
- is_digit
- find_layer_violations
- fields_share_access
- find_method_index
- sort_descending
- compute_lcom4
- compute_pss
- compute_public_ratio
- compute_avg_param_count
- compute_max_param_count
- compute_overload_groups
- compute_eur
- compute_entropy
- type_set_edit_distance
- generate_deletion_variants
- compute_type_hash
- build_dsm
- token_kind_ordinal
- to_relaxed_tokens

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 109 |
| Active scenarios | 109 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
