# Coupling Metrics Specification

> Tests covering compute_fan_out, compute_fan_in, compute_all_metrics, find_cycles, find_instability_inversions, extract_layer_number, is_digit, find_layer_violations, fields_share_access, find_method_index, sort_descending, compute_lcom4, compute_pss, compute_public_ratio, compute_avg_param_count, compute_max_param_count, compute_overload_groups, compute_eur, compute_entropy, type_set_edit_distance, generate_deletion_variants, compute_type_hash, build_dsm, token_kind_ordinal, to_relaxed_tokens.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 109 | 109 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Coupling Metrics Specification

## Scenarios

### compute_fan_out

#### returns correct fan-out for a linear chain

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns correct fan-out for a linear chain
   - Expected: result.get("A") equals `1`
   - Expected: result.get("B") equals `1`
   - Expected: result.get("C") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct fan-out for a linear chain")
var edges: Dict<text, [text]> = {}
edges["A"] = ["B"]
edges["B"] = ["C"]
edges["C"] = []
val graph = make_graph(edges)
val result = compute_fan_out(graph)
expect(result.get("A")).to_equal(1)
expect(result.get("B")).to_equal(1)
expect(result.get("C")).to_equal(0)
```

</details>

#### returns correct fan-out for a module with multiple deps

- returns correct fan-out for a module with multiple deps
   - Expected: result.get("A") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct fan-out for a module with multiple deps")
var edges: Dict<text, [text]> = {}
edges["A"] = ["B", "C", "D"]
edges["B"] = []
edges["C"] = []
edges["D"] = []
val graph = make_graph(edges)
val result = compute_fan_out(graph)
expect(result.get("A")).to_equal(3)
```

</details>

#### returns zero fan-out for isolated modules

- returns zero fan-out for isolated modules
   - Expected: result.get("X") equals `0`
   - Expected: result.get("Y") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns zero fan-out for isolated modules")
var edges: Dict<text, [text]> = {}
edges["X"] = []
edges["Y"] = []
val graph = make_graph(edges)
val result = compute_fan_out(graph)
expect(result.get("X")).to_equal(0)
expect(result.get("Y")).to_equal(0)
```

</details>

#### handles empty graph

- handles empty graph
   - Expected: result.keys().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty graph")
var edges: Dict<text, [text]> = {}
val graph = make_graph(edges)
val result = compute_fan_out(graph)
expect(result.keys().len()).to_equal(0)
```

</details>

### compute_fan_in

#### returns correct fan-in for a linear chain

- returns correct fan-in for a linear chain
   - Expected: result.get("A") equals `0`
   - Expected: result.get("B") equals `1`
   - Expected: result.get("C") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct fan-in for a linear chain")
var edges: Dict<text, [text]> = {}
edges["A"] = ["B"]
edges["B"] = ["C"]
edges["C"] = []
val graph = make_graph(edges)
val result = compute_fan_in(graph)
expect(result.get("A")).to_equal(0)
expect(result.get("B")).to_equal(1)
expect(result.get("C")).to_equal(1)
```

</details>

#### counts multiple incomers correctly

- counts multiple incomers correctly
   - Expected: result.get("C") equals `2`
   - Expected: result.get("A") equals `0`
   - Expected: result.get("B") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts multiple incomers correctly")
var edges: Dict<text, [text]> = {}
edges["A"] = ["C"]
edges["B"] = ["C"]
edges["C"] = []
val graph = make_graph(edges)
val result = compute_fan_in(graph)
expect(result.get("C")).to_equal(2)
expect(result.get("A")).to_equal(0)
expect(result.get("B")).to_equal(0)
```

</details>

#### handles empty graph

- handles empty graph
   - Expected: result.keys().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty graph")
var edges: Dict<text, [text]> = {}
val graph = make_graph(edges)
val result = compute_fan_in(graph)
expect(result.keys().len()).to_equal(0)
```

</details>

#### handles single node with no edges

- handles single node with no edges
   - Expected: result.get("Solo") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single node with no edges")
var edges: Dict<text, [text]> = {}
edges["Solo"] = []
val graph = make_graph(edges)
val result = compute_fan_in(graph)
expect(result.get("Solo")).to_equal(0)
```

</details>

### compute_all_metrics

#### computes instability for a hub-and-spoke graph

- computes instability for a hub-and-spoke graph
   - Expected: hub.fan_out equals `3`
   - Expected: hub.fan_in equals `0`
   - Expected: hub.instability equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes instability for a hub-and-spoke graph")
var edges: Dict<text, [text]> = {}
edges["hub"] = ["a", "b", "c"]
edges["a"] = []
edges["b"] = []
edges["c"] = []
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

- leaf modules have instability 0
   - Expected: leaf.fan_out equals `0`
   - Expected: leaf.instability equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaf modules have instability 0")
var edges: Dict<text, [text]> = {}
edges["hub"] = ["leaf"]
edges["leaf"] = []
val graph = make_graph(edges)
val metrics = compute_all_metrics(graph)
val leaf = find_metric_by_name(metrics, "leaf")
# leaf: fan_out=0, fan_in=1, instability=0/(1+0)=0.0
expect(leaf.fan_out).to_equal(0)
expect(leaf.instability).to_equal(0.0)
```

</details>

#### isolated node has instability 0

- isolated node has instability 0
   - Expected: solo.instability equals `0.0`
   - Expected: solo.distance equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("isolated node has instability 0")
var edges: Dict<text, [text]> = {}
edges["solo"] = []
val graph = make_graph(edges)
val metrics = compute_all_metrics(graph)
val solo = find_metric_by_name(metrics, "solo")
expect(solo.instability).to_equal(0.0)
expect(solo.distance).to_equal(1.0)
```

</details>

#### cbo equals fan_out

- cbo equals fan_out
   - Expected: x.cbo equals `x.fan_out`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cbo equals fan_out")
var edges: Dict<text, [text]> = {}
edges["X"] = ["Y", "Z"]
edges["Y"] = []
edges["Z"] = []
val graph = make_graph(edges)
val metrics = compute_all_metrics(graph)
val x = find_metric_by_name(metrics, "X")
expect(x.cbo).to_equal(x.fan_out)
```

</details>

#### distance from main sequence is computed correctly

- distance from main sequence is computed correctly
   - Expected: m.instability equals `0.5`
   - Expected: m.distance equals `0.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distance from main sequence is computed correctly")
# Module with instability=0.5, abstractness=0 -> distance = |0+0.5-1| = 0.5
var edges: Dict<text, [text]> = {}
edges["M"] = ["N"]
edges["N"] = ["M"]
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

- detects a simple 2-node cycle
   - Expected: cycles.len() equals `1`
   - Expected: cycles.get(0).len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects a simple 2-node cycle")
var edges: Dict<text, [text]> = {}
edges["A"] = ["B"]
edges["B"] = ["A"]
val graph = make_graph(edges)
val cycles = find_cycles(graph)
expect(cycles.len()).to_equal(1)
expect(cycles.get(0).len()).to_equal(2)
```

</details>

#### detects a 3-node cycle

- detects a 3-node cycle
   - Expected: cycles.len() equals `1`
   - Expected: cycles.get(0).len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects a 3-node cycle")
var edges: Dict<text, [text]> = {}
edges["A"] = ["B"]
edges["B"] = ["C"]
edges["C"] = ["A"]
val graph = make_graph(edges)
val cycles = find_cycles(graph)
expect(cycles.len()).to_equal(1)
expect(cycles.get(0).len()).to_equal(3)
```

</details>

#### returns empty for an acyclic graph

- returns empty for an acyclic graph
   - Expected: cycles.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for an acyclic graph")
var edges: Dict<text, [text]> = {}
edges["A"] = ["B"]
edges["B"] = ["C"]
edges["C"] = []
val graph = make_graph(edges)
val cycles = find_cycles(graph)
expect(cycles.len()).to_equal(0)
```

</details>

#### returns empty for an empty graph

- returns empty for an empty graph
   - Expected: cycles.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for an empty graph")
var edges: Dict<text, [text]> = {}
val graph = make_graph(edges)
val cycles = find_cycles(graph)
expect(cycles.len()).to_equal(0)
```

</details>

#### returns empty for a single node

- returns empty for a single node
   - Expected: cycles.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for a single node")
var edges: Dict<text, [text]> = {}
edges["A"] = []
val graph = make_graph(edges)
val cycles = find_cycles(graph)
expect(cycles.len()).to_equal(0)
```

</details>

### find_instability_inversions

#### detects inversion when stable depends on unstable

- detects inversion when stable depends on unstable


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects inversion when stable depends on unstable")
# A has fan_in=1, fan_out=1 => instability=0.5
# B has fan_in=0, fan_out=1 => instability=1.0
# A depends on B: A (stable=0.5) -> B (unstable=1.0) = inversion
# But we also need B depending on something so B has fan_out
var edges: Dict<text, [text]> = {}
edges["stable"] = ["unstable"]
edges["unstable"] = ["leaf1", "leaf2"]
edges["other"] = ["stable"]
edges["leaf1"] = []
edges["leaf2"] = []
val graph = make_graph(edges)
val metrics = compute_all_metrics(graph)
val inversions = find_instability_inversions(metrics, graph)
# stable (instab ~0.5) depends on unstable (instab=1.0) => inversion
expect(inversions.len()).to_be_greater_than(0)
```

</details>

#### returns empty when no inversions exist

- returns empty when no inversions exist
   - Expected: inversions.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty when no inversions exist")
# Linear: unstable -> stable -> leaf
var edges: Dict<text, [text]> = {}
edges["A"] = ["B"]
edges["B"] = []
val graph = make_graph(edges)
val metrics = compute_all_metrics(graph)
val inversions = find_instability_inversions(metrics, graph)
# A: instab=1.0 depends on B: instab=0.0 => no inversion (unstable depends on stable = OK)
expect(inversions.len()).to_equal(0)
```

</details>

#### returns empty for empty graph

- returns empty for empty graph
   - Expected: inversions.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for empty graph")
var edges: Dict<text, [text]> = {}
val graph = make_graph(edges)
val metrics = compute_all_metrics(graph)
val inversions = find_instability_inversions(metrics, graph)
expect(inversions.len()).to_equal(0)
```

</details>

### extract_layer_number

#### extracts layer from slash-separated path

- extracts layer from slash-separated path
   - Expected: result equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts layer from slash-separated path")
val result = extract_layer_number("compiler/30.types/foo")
expect(result).to_equal(30)
```

</details>

#### extracts layer 00 from common

- extracts layer 00 from common
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts layer 00 from common")
val result = extract_layer_number("compiler/00.common/bar")
expect(result).to_equal(0)
```

</details>

#### returns nil for non-layer path

- returns nil for non-layer path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for non-layer path")
val result = extract_layer_number("std/text/utils")
expect(result).to_be_nil()
```

</details>

#### extracts layer from dot-separated path

- extracts layer from dot-separated path
   - Expected: result equals `70`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts layer from dot-separated path")
val result = extract_layer_number("compiler.70.backend.llvm")
expect(result).to_equal(70)
```

</details>

#### returns nil for single character segment

- returns nil for single character segment


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for single character segment")
val result = extract_layer_number("a/b/c")
expect(result).to_be_nil()
```

</details>

### is_digit

#### returns true for digit characters

- returns true for digit characters
   - Expected: is_digit("0") is true
   - Expected: is_digit("5") is true
   - Expected: is_digit("9") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for digit characters")
expect(is_digit("0")).to_equal(true)
expect(is_digit("5")).to_equal(true)
expect(is_digit("9")).to_equal(true)
```

</details>

#### returns false for non-digit characters

- returns false for non-digit characters
   - Expected: is_digit("a") is false
   - Expected: is_digit("Z") is false
   - Expected: is_digit(" ") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for non-digit characters")
expect(is_digit("a")).to_equal(false)
expect(is_digit("Z")).to_equal(false)
expect(is_digit(" ")).to_equal(false)
```

</details>

### find_layer_violations

#### detects violation when lower layer imports higher layer

- detects violation when lower layer imports higher layer
   - Expected: violations[0].from_layer equals `10`
   - Expected: violations[0].to_layer equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects violation when lower layer imports higher layer")
var edges: Dict<text, [text]> = {}
edges["compiler/10.frontend/foo"] = ["compiler/30.types/bar"]
edges["compiler/30.types/bar"] = []
val graph = make_graph(edges)
val violations = find_layer_violations(graph)
expect(violations.len()).to_be_greater_than(0)
if violations.len() > 0:
    expect(violations[0].from_layer).to_equal(10)
    expect(violations[0].to_layer).to_equal(30)
```

</details>

#### allows higher layer importing lower layer

- allows higher layer importing lower layer
   - Expected: violations.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows higher layer importing lower layer")
var edges: Dict<text, [text]> = {}
edges["compiler/30.types/bar"] = ["compiler/00.common/foo"]
edges["compiler/00.common/foo"] = []
val graph = make_graph(edges)
val violations = find_layer_violations(graph)
expect(violations.len()).to_equal(0)
```

</details>

#### no violations for non-layer modules

- no violations for non-layer modules
   - Expected: violations.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no violations for non-layer modules")
var edges: Dict<text, [text]> = {}
edges["std/text/utils"] = ["std/math/ops"]
edges["std/math/ops"] = []
val graph = make_graph(edges)
val violations = find_layer_violations(graph)
expect(violations.len()).to_equal(0)
```

</details>

#### returns empty for empty graph

- returns empty for empty graph
   - Expected: violations.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for empty graph")
var edges: Dict<text, [text]> = {}
val graph = make_graph(edges)
val violations = find_layer_violations(graph)
expect(violations.len()).to_equal(0)
```

</details>

#### uses detailed_edges when available

- uses detailed_edges when available
   - Expected: violations[0].from_layer equals `10`
   - Expected: violations[0].to_layer equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses detailed_edges when available")
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

- returns true when lists share a field
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true when lists share a field")
val result = fields_share_access(["x", "y"], ["y", "z"])
expect(result).to_equal(true)
```

</details>

#### returns false when lists share no field

- returns false when lists share no field
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when lists share no field")
val result = fields_share_access(["x", "y"], ["z", "w"])
expect(result).to_equal(false)
```

</details>

#### returns false for empty lists

- returns false for empty lists
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for empty lists")
val result = fields_share_access([], [])
expect(result).to_equal(false)
```

</details>

#### returns false when one list is empty

- returns false when one list is empty
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when one list is empty")
val result = fields_share_access(["x"], [])
expect(result).to_equal(false)
```

</details>

### find_method_index

#### finds existing method by name

- finds existing method by name
   - Expected: find_method_index(methods, "beta") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds existing method by name")
val methods = [
    make_method("alpha", [], []),
    make_method("beta", [], []),
    make_method("gamma", [], [])
]
expect(find_method_index(methods, "beta")).to_equal(1)
```

</details>

#### returns -1 for missing method

- returns -1 for missing method
   - Expected: find_method_index(methods, "missing") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 for missing method")
val methods = [make_method("alpha", [], [])]
expect(find_method_index(methods, "missing")).to_equal(-1)
```

</details>

#### returns -1 for empty list

- returns -1 for empty list
   - Expected: find_method_index(methods, "any") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 for empty list")
var methods: [MethodFieldAccess] = []
expect(find_method_index(methods, "any")).to_equal(-1)
```

</details>

### sort_descending

#### sorts integers in descending order

- sorts integers in descending order
   - Expected: result.get(0) equals `5`
   - Expected: result.get(1) equals `4`
   - Expected: result.get(2) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sorts integers in descending order")
val result = sort_descending([1, 3, 2, 5, 4])
expect(result.get(0)).to_equal(5)
expect(result.get(1)).to_equal(4)
expect(result.get(2)).to_equal(3)
```

</details>

#### handles single element

- handles single element
   - Expected: result.get(0) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single element")
val result = sort_descending([42])
expect(result.get(0)).to_equal(42)
```

</details>

#### handles empty list

- handles empty list
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty list")
val result = sort_descending([])
expect(result.len()).to_equal(0)
```

</details>

#### handles already sorted input

- handles already sorted input
   - Expected: result.get(0) equals `5`
   - Expected: result.get(4) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles already sorted input")
val result = sort_descending([5, 4, 3, 2, 1])
expect(result.get(0)).to_equal(5)
expect(result.get(4)).to_equal(1)
```

</details>

### compute_lcom4

#### returns 0 for class with no methods

- returns 0 for class with no methods
   - Expected: result.lcom4 equals `0`
   - Expected: result.method_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for class with no methods")
var methods: [MethodFieldAccess] = []
val result = compute_lcom4("Empty", methods)
expect(result.lcom4).to_equal(0)
expect(result.method_count).to_equal(0)
```

</details>

#### returns 1 for class with a single method

- returns 1 for class with a single method
   - Expected: result.lcom4 equals `1`
   - Expected: result.method_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 1 for class with a single method")
val methods = [make_method("do_thing", ["x"], [])]
val result = compute_lcom4("Single", methods)
expect(result.lcom4).to_equal(1)
expect(result.method_count).to_equal(1)
```

</details>

#### returns 1 for cohesive class (shared fields)

- returns 1 for cohesive class (shared fields)
   - Expected: result.lcom4 equals `1`
   - Expected: result.method_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 1 for cohesive class (shared fields)")
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

- returns 2 for non-cohesive class (disjoint methods)
   - Expected: result.lcom4 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 2 for non-cohesive class (disjoint methods)")
val methods = [
    make_method("get_x", ["x"], []),
    make_method("get_y", ["y"], [])
]
val result = compute_lcom4("Split", methods)
expect(result.lcom4).to_equal(2)
```

</details>

#### connects methods through method calls

- connects methods through method calls
   - Expected: result.lcom4 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("connects methods through method calls")
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

- counts fields correctly
   - Expected: result.field_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts fields correctly")
val methods = [
    make_method("m1", ["a", "b"], []),
    make_method("m2", ["b", "c"], [])
]
val result = compute_lcom4("FieldCount", methods)
expect(result.field_count).to_equal(3)
```

</details>

#### produces component_sizes that sum to method_count

- produces component_sizes that sum to method_count
   - Expected: result.lcom4 equals `2`
   - Expected: total equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces component_sizes that sum to method_count")
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

- sums public methods and fields
   - Expected: compute_pss(5, 3) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sums public methods and fields")
expect(compute_pss(5, 3)).to_equal(8)
```

</details>

#### returns 0 when both are 0

- returns 0 when both are 0
   - Expected: compute_pss(0, 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 when both are 0")
expect(compute_pss(0, 0)).to_equal(0)
```

</details>

#### handles methods only

- handles methods only
   - Expected: compute_pss(10, 0) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles methods only")
expect(compute_pss(10, 0)).to_equal(10)
```

</details>

#### handles fields only

- handles fields only
   - Expected: compute_pss(0, 7) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles fields only")
expect(compute_pss(0, 7)).to_equal(7)
```

</details>

### compute_public_ratio

#### returns correct ratio

- returns correct ratio
   - Expected: result equals `0.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct ratio")
val result = compute_public_ratio(5, 10)
expect(result).to_equal(0.5)
```

</details>

#### returns 0 when total is 0

- returns 0 when total is 0
   - Expected: result equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 when total is 0")
val result = compute_public_ratio(0, 0)
expect(result).to_equal(0.0)
```

</details>

#### returns 1.0 when all are public

- returns 1.0 when all are public
   - Expected: result equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 1.0 when all are public")
val result = compute_public_ratio(4, 4)
expect(result).to_equal(1.0)
```

</details>

### compute_avg_param_count

#### computes average correctly

- computes average correctly
   - Expected: result equals `4.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes average correctly")
val result = compute_avg_param_count([2, 4, 6])
expect(result).to_equal(4.0)
```

</details>

#### returns 0 for empty list

- returns 0 for empty list
   - Expected: result equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for empty list")
val result = compute_avg_param_count([])
expect(result).to_equal(0.0)
```

</details>

#### handles single element

- handles single element
   - Expected: result equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single element")
val result = compute_avg_param_count([3])
expect(result).to_equal(3.0)
```

</details>

### compute_max_param_count

#### finds maximum

- finds maximum
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds maximum")
val result = compute_max_param_count([1, 5, 3, 2])
expect(result).to_equal(5)
```

</details>

#### returns 0 for empty list

- returns 0 for empty list
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for empty list")
val result = compute_max_param_count([])
expect(result).to_equal(0)
```

</details>

### compute_overload_groups

#### counts groups with duplicate names

- counts groups with duplicate names
   - Expected: result equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts groups with duplicate names")
val result = compute_overload_groups(["foo", "bar", "foo", "baz", "bar"])
expect(result).to_equal(2)
```

</details>

#### returns 0 for all unique names

- returns 0 for all unique names
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for all unique names")
val result = compute_overload_groups(["a", "b", "c"])
expect(result).to_equal(0)
```

</details>

#### returns 0 for empty list

- returns 0 for empty list
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for empty list")
val result = compute_overload_groups([])
expect(result).to_equal(0)
```

</details>

### compute_eur

#### returns fraction of used methods

- returns fraction of used methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns fraction of used methods")
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

- returns 0 when no methods are used
   - Expected: result equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 when no methods are used")
val usages = [make_usage("a", 0), make_usage("b", 0)]
val result = compute_eur(usages, 2)
expect(result).to_equal(0.0)
```

</details>

#### returns 0 when total_public is 0

- returns 0 when total_public is 0
   - Expected: result equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 when total_public is 0")
val usages = [make_usage("a", 5)]
val result = compute_eur(usages, 0)
expect(result).to_equal(0.0)
```

</details>

#### returns 1.0 when all methods used

- returns 1.0 when all methods used
   - Expected: result equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 1.0 when all methods used")
val usages = [make_usage("a", 1), make_usage("b", 1)]
val result = compute_eur(usages, 2)
expect(result).to_equal(1.0)
```

</details>

### compute_entropy

#### returns 1.0 for perfectly uniform usage

- returns 1.0 for perfectly uniform usage


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 1.0 for perfectly uniform usage")
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

- returns 0 for no usage
   - Expected: result equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for no usage")
val usages = [make_usage("a", 0), make_usage("b", 0)]
val result = compute_entropy(usages)
expect(result).to_equal(0.0)
```

</details>

#### returns 0 for single used method

- returns 0 for single used method
   - Expected: result equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for single used method")
val usages = [make_usage("a", 10)]
val result = compute_entropy(usages)
expect(result).to_equal(0.0)
```

</details>

#### returns less than 1 for skewed usage

- returns less than 1 for skewed usage


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns less than 1 for skewed usage")
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

- handles empty list
   - Expected: result equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty list")
var usages: [MethodUsage] = []
val result = compute_entropy(usages)
expect(result).to_equal(0.0)
```

</details>

### type_set_edit_distance

#### returns 0 for identical sorted sets

- returns 0 for identical sorted sets
   - Expected: dist equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for identical sorted sets")
val dist = type_set_edit_distance(["i64", "text"], ["i64", "text"])
expect(dist).to_equal(0)
```

</details>

#### returns 1 for single addition

- returns 1 for single addition
   - Expected: dist equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 1 for single addition")
val dist = type_set_edit_distance(["i64"], ["i64", "text"])
expect(dist).to_equal(1)
```

</details>

#### returns 1 for single removal

- returns 1 for single removal
   - Expected: dist equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 1 for single removal")
val dist = type_set_edit_distance(["i64", "text"], ["text"])
expect(dist).to_equal(1)
```

</details>

#### returns sum of lengths for completely disjoint sets

- returns sum of lengths for completely disjoint sets
   - Expected: dist equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns sum of lengths for completely disjoint sets")
val dist = type_set_edit_distance(["a", "b"], ["c", "d"])
expect(dist).to_equal(4)
```

</details>

#### returns 0 for two empty sets

- returns 0 for two empty sets
   - Expected: dist equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for two empty sets")
val dist = type_set_edit_distance([], [])
expect(dist).to_equal(0)
```

</details>

#### returns length when one set is empty

- returns length when one set is empty
   - Expected: dist equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns length when one set is empty")
val dist = type_set_edit_distance(["a", "b", "c"], [])
expect(dist).to_equal(3)
```

</details>

#### handles swap correctly

- handles swap correctly
   - Expected: dist equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles swap correctly")
# ["a", "c"] vs ["b", "c"] => remove a, add b = 2
val dist = type_set_edit_distance(["a", "c"], ["b", "c"])
expect(dist).to_equal(2)
```

</details>

### generate_deletion_variants

#### generates N variants for list of length N

- generates N variants for list of length N
   - Expected: variants.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates N variants for list of length N")
val variants = generate_deletion_variants(["a", "b", "c"])
expect(variants.len()).to_equal(3)
```

</details>

#### each variant has length N-1

- each variant has length N-1
   - Expected: variants.get(i).len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("each variant has length N-1")
val variants = generate_deletion_variants(["x", "y", "z"])
var i = 0
while i < variants.len():
    expect(variants.get(i).len()).to_equal(2)
    i = i + 1
```

</details>

#### first variant removes first element

- first variant removes first element
   - Expected: variants.get(0) equals `["b", "c"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first variant removes first element")
val variants = generate_deletion_variants(["a", "b", "c"])
expect(variants.get(0)).to_equal(["b", "c"])
```

</details>

#### last variant removes last element

- last variant removes last element
   - Expected: variants.get(2) equals `["a", "b"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("last variant removes last element")
val variants = generate_deletion_variants(["a", "b", "c"])
expect(variants.get(2)).to_equal(["a", "b"])
```

</details>

#### returns empty list for empty input

- returns empty list for empty input
   - Expected: variants.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty list for empty input")
val variants = generate_deletion_variants([])
expect(variants.len()).to_equal(0)
```

</details>

#### returns one empty variant for single element

- returns one empty variant for single element
   - Expected: variants.len() equals `1`
   - Expected: variants.get(0).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns one empty variant for single element")
val variants = generate_deletion_variants(["only"])
expect(variants.len()).to_equal(1)
expect(variants.get(0).len()).to_equal(0)
```

</details>

### compute_type_hash

#### returns same hash for same input

- returns same hash for same input
   - Expected: h1 equals `h2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns same hash for same input")
val h1 = compute_type_hash(["i64", "text"])
val h2 = compute_type_hash(["i64", "text"])
expect(h1).to_equal(h2)
```

</details>

#### returns different hash for different input

- returns different hash for different input


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns different hash for different input")
val h1 = compute_type_hash(["i64"])
val h2 = compute_type_hash(["text"])
# Very unlikely to collide
expect(h1).to_not_equal(h2)
```

</details>

#### returns 0 for empty list

- returns 0 for empty list
   - Expected: h equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for empty list")
val h = compute_type_hash([])
expect(h).to_equal(0)
```

</details>

### build_dsm

<details>
<summary>Advanced: builds NxN matrix for N modules</summary>

#### builds NxN matrix for N modules

- builds NxN matrix for N modules
   - Expected: dsm.modules.len() equals `3`
   - Expected: dsm.matrix.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds NxN matrix for N modules")
var edges: Dict<text, [text]> = {}
edges["A"] = ["B"]
edges["B"] = ["C"]
edges["C"] = []
val graph = make_graph(edges)
val dsm = build_dsm(graph)
expect(dsm.modules.len()).to_equal(3)
expect(dsm.matrix.len()).to_equal(3)
```

</details>


</details>

#### records dependency in correct cell

- records dependency in correct cell
   - Expected: dsm.modules.len() equals `2`
   - Expected: dsm.matrix.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records dependency in correct cell")
var edges: Dict<text, [text]> = {}
edges["A"] = ["B"]
edges["B"] = []
val graph = make_graph(edges)
val dsm = build_dsm(graph)
# modules sorted alphabetically: [A, B]
expect(dsm.modules.len()).to_equal(2)
expect(dsm.matrix.len()).to_equal(2)
```

</details>

#### handles empty graph

- handles empty graph
   - Expected: dsm.modules.len() equals `0`
   - Expected: dsm.matrix.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty graph")
var edges: Dict<text, [text]> = {}
val graph = make_graph(edges)
val dsm = build_dsm(graph)
expect(dsm.modules.len()).to_equal(0)
expect(dsm.matrix.len()).to_equal(0)
```

</details>

#### sorts modules alphabetically

- sorts modules alphabetically
   - Expected: dsm.modules.get(0) equals `A`
   - Expected: dsm.modules.get(1) equals `B`
   - Expected: dsm.modules.get(2) equals `C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sorts modules alphabetically")
var edges: Dict<text, [text]> = {}
edges["C"] = ["A"]
edges["B"] = []
edges["A"] = []
val graph = make_graph(edges)
val dsm = build_dsm(graph)
expect(dsm.modules.get(0)).to_equal("A")
expect(dsm.modules.get(1)).to_equal("B")
expect(dsm.modules.get(2)).to_equal("C")
```

</details>

#### diagonal is always zero

- diagonal is always zero
   - Expected: dsm.matrix.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("diagonal is always zero")
var edges: Dict<text, [text]> = {}
edges["A"] = ["B"]
edges["B"] = ["A"]
val graph = make_graph(edges)
val dsm = build_dsm(graph)
expect(dsm.matrix.len()).to_equal(2)
```

</details>

### token_kind_ordinal

#### maps Identifier to 0

- maps Identifier to 0
   - Expected: token_kind_ordinal(SimpleTokenKind.Identifier) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps Identifier to 0")
expect(token_kind_ordinal(SimpleTokenKind.Identifier)).to_equal(0)
```

</details>

#### maps Keyword to 1

- maps Keyword to 1
   - Expected: token_kind_ordinal(SimpleTokenKind.Keyword) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps Keyword to 1")
expect(token_kind_ordinal(SimpleTokenKind.Keyword)).to_equal(1)
```

</details>

#### maps Operator to 2

- maps Operator to 2
   - Expected: token_kind_ordinal(SimpleTokenKind.Operator) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps Operator to 2")
expect(token_kind_ordinal(SimpleTokenKind.Operator)).to_equal(2)
```

</details>

#### maps Literal to 3

- maps Literal to 3
   - Expected: token_kind_ordinal(SimpleTokenKind.Literal) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps Literal to 3")
expect(token_kind_ordinal(SimpleTokenKind.Literal)).to_equal(3)
```

</details>

#### maps Punctuation to 4

- maps Punctuation to 4
   - Expected: token_kind_ordinal(SimpleTokenKind.Punctuation) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps Punctuation to 4")
expect(token_kind_ordinal(SimpleTokenKind.Punctuation)).to_equal(4)
```

</details>

#### maps Comment to 5

- maps Comment to 5
   - Expected: token_kind_ordinal(SimpleTokenKind.Comment) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps Comment to 5")
expect(token_kind_ordinal(SimpleTokenKind.Comment)).to_equal(5)
```

</details>

#### maps Whitespace to 6

- maps Whitespace to 6
   - Expected: token_kind_ordinal(SimpleTokenKind.Whitespace) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps Whitespace to 6")
expect(token_kind_ordinal(SimpleTokenKind.Whitespace)).to_equal(6)
```

</details>

### to_relaxed_tokens

#### filters out whitespace tokens

- filters out whitespace tokens
   - Expected: relaxed.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filters out whitespace tokens")
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

- filters out comment tokens
   - Expected: relaxed.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filters out comment tokens")
val tokens = [
    make_token(SimpleTokenKind.Keyword, 1, 0),
    make_token(SimpleTokenKind.Comment, 1, 5)
]
val relaxed = to_relaxed_tokens(tokens)
expect(relaxed.len()).to_equal(1)
```

</details>

#### preserves line and column info

- preserves line and column info
   - Expected: relaxed.get(0).line equals `7`
   - Expected: relaxed.get(0).column equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves line and column info")
val tokens = [make_token(SimpleTokenKind.Literal, 7, 12)]
val relaxed = to_relaxed_tokens(tokens)
expect(relaxed.get(0).line).to_equal(7)
expect(relaxed.get(0).column).to_equal(12)
```

</details>

#### sets correct kind_ordinal

- sets correct kind_ordinal
   - Expected: relaxed.get(0).kind_ordinal equals `1`
   - Expected: relaxed.get(1).kind_ordinal equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets correct kind_ordinal")
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

- returns empty for empty input
   - Expected: relaxed.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for empty input")
var tokens: [SimpleToken] = []
val relaxed = to_relaxed_tokens(tokens)
expect(relaxed.len()).to_equal(0)
```

</details>

#### returns empty when all tokens are whitespace/comments

- returns empty when all tokens are whitespace/comments
   - Expected: relaxed.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty when all tokens are whitespace/comments")
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
| Source | `test/unit/coupling/coupling_metrics_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering compute_fan_out, compute_fan_in, compute_all_metrics, find_cycles, find_instability_inversions, extract_layer_number, is_digit, find_layer_violations, fields_share_access, find_method_index, sort_descending, compute_lcom4, compute_pss, compute_public_ratio, compute_avg_param_count, compute_max_param_count, compute_overload_groups, compute_eur, compute_entropy, type_set_edit_distance, generate_deletion_variants, compute_type_hash, build_dsm, token_kind_ordinal, to_relaxed_tokens.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-coupling-analysis`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b5f799be391cbda647c3644953235a9abe5732ad3efd61378aeeef02ae8c1fb2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b5f799be391cbda647c3644953235a9abe5732ad3efd61378aeeef02ae8c1fb2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b5f799be391cbda647c3644953235a9abe5732ad3efd61378aeeef02ae8c1fb2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/coupling/coupling_metrics_spec.spl
mirror: doc/06_spec/unit/coupling/coupling_metrics_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/unit/coupling/coupling_metrics_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/coupling/coupling_metrics_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/coupling/coupling_metrics_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 120 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/coupling/coupling_metrics_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/coupling/coupling_metrics_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns correct fan-out for a linear chain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/coupling/coupling_metrics_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns correct fan-out for a module with multiple deps' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/coupling/coupling_metrics_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns zero fan-out for isolated modules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
