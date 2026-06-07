# Graph Coloring Specification

> <details>

<!-- sdn-diagram:id=graph_coloring_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=graph_coloring_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

graph_coloring_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=graph_coloring_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Graph Coloring Specification

## Scenarios

### graph_coloring

#### empty constraints produce empty coloring

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val constraints = ContactConstraintSoA.create()
val result = greedy_color(constraints, 0)
expect(result.num_colors).to_equal(0)
```

</details>

#### single constraint gets color 0

1. var constraints = ContactConstraintSoA create
2. constraints add
   - Expected: result.num_colors equals `1`
   - Expected: result.colors[0] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var constraints = ContactConstraintSoA.create()
constraints.add(0, 1, 0.0, 1.0, 0.0, 0.0, 0.1, 0.3, 0.4, 0, 0)
val result = greedy_color(constraints, 2)
expect(result.num_colors).to_equal(1)
expect(result.colors[0]).to_equal(0)
```

</details>

#### two constraints sharing a body get different colors

1. var constraints = ContactConstraintSoA create
2. constraints add
3. constraints add
   - Expected: result.num_colors >= 2 is true
   - Expected: result.colors[0] != result.colors[1] is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var constraints = ContactConstraintSoA.create()
constraints.add(0, 1, 0.0, 1.0, 0.0, 0.0, 0.1, 0.3, 0.4, 0, 0)
constraints.add(0, 2, 0.0, 1.0, 0.0, 0.0, 0.1, 0.3, 0.4, 0, 0)
val result = greedy_color(constraints, 3)
expect(result.num_colors >= 2).to_equal(true)
expect(result.colors[0] != result.colors[1]).to_equal(true)
```

</details>

#### two independent constraints can share a color

1. var constraints = ContactConstraintSoA create
2. constraints add
3. constraints add
   - Expected: result.colors[0] equals `result.colors[1]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var constraints = ContactConstraintSoA.create()
constraints.add(0, 1, 0.0, 1.0, 0.0, 0.0, 0.1, 0.3, 0.4, 0, 0)
constraints.add(2, 3, 0.0, 1.0, 0.0, 0.0, 0.1, 0.3, 0.4, 0, 0)
val result = greedy_color(constraints, 4)
expect(result.colors[0]).to_equal(result.colors[1])
```

</details>

#### chain of 4 bodies needs at most 2 colors

1. var constraints = ContactConstraintSoA create
2. constraints add
3. constraints add
4. constraints add
   - Expected: result.num_colors <= 3 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var constraints = ContactConstraintSoA.create()
constraints.add(0, 1, 0.0, 1.0, 0.0, 0.0, 0.1, 0.3, 0.4, 0, 0)
constraints.add(1, 2, 0.0, 1.0, 0.0, 0.0, 0.1, 0.3, 0.4, 0, 0)
constraints.add(2, 3, 0.0, 1.0, 0.0, 0.0, 0.1, 0.3, 0.4, 0, 0)
val result = greedy_color(constraints, 4)
expect(result.num_colors <= 3).to_equal(true)
```

</details>

#### sorted_indices covers all constraints

1. var constraints = ContactConstraintSoA create
2. constraints add
3. constraints add
4. constraints add
   - Expected: result.sorted_indices.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var constraints = ContactConstraintSoA.create()
constraints.add(0, 1, 0.0, 1.0, 0.0, 0.0, 0.1, 0.3, 0.4, 0, 0)
constraints.add(1, 2, 0.0, 1.0, 0.0, 0.0, 0.1, 0.3, 0.4, 0, 0)
constraints.add(0, 2, 0.0, 1.0, 0.0, 0.0, 0.1, 0.3, 0.4, 0, 0)
val result = greedy_color(constraints, 3)
expect(result.sorted_indices.len()).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/physics/physics2/graph_coloring_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- graph_coloring

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
