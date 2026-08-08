# Coupling Analysis Specification

> <details>

<!-- sdn-diagram:id=coupling_analysis_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=coupling_analysis_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

coupling_analysis_spec -> std
coupling_analysis_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=coupling_analysis_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Coupling Analysis Specification

## Scenarios

### Coupling Analysis

#### computes coupling metrics for a dependency graph

- edges = edges set
- edges = edges set
- edges = edges set
   - Expected: metrics.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
edges = edges.set("app", ["lib", "compiler"])
edges = edges.set("lib", [])
edges = edges.set("compiler", ["lib"])

val metrics = compute_all_metrics(graph(edges))

expect(metrics.len()).to_equal(3)
expect(metrics[0].module_name.len()).to_be_greater_than(0)
```

</details>

#### detects cohesion split with LCOM4

- method access
- method access
- method access
   - Expected: result.method_count equals `3`
   - Expected: result.lcom4 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val methods = [
    method_access("read", ["path"], []),
    method_access("write", ["path"], []),
    method_access("render", ["canvas"], [])
]

val result = compute_lcom4("QualitySmoke", methods)

expect(result.method_count).to_equal(3)
expect(result.lcom4).to_equal(2)
```

</details>

#### flags lower layer importing a higher layer

- edges = edges set
- edges = edges set
   - Expected: violations.len() equals `1`
   - Expected: violations[0].from_layer equals `10`
   - Expected: violations[0].to_layer equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var edges: Dict<text, [text]> = {}
edges = edges.set("compiler/10.frontend/parser", ["compiler/30.types/checker"])
edges = edges.set("compiler/30.types/checker", [])

val violations = find_layer_violations(graph(edges))

expect(violations.len()).to_equal(1)
expect(violations[0].from_layer).to_equal(10)
expect(violations[0].to_layer).to_equal(30)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/quality/coupling_analysis_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Coupling Analysis

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
