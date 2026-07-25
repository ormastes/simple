# Test Dep Graph Specification

> 1. dir create all

<!-- sdn-diagram:id=test_dep_graph_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_dep_graph_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_dep_graph_spec -> std
test_dep_graph_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_dep_graph_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Dep Graph Specification

## Scenarios

### TestRunner dependency graph

#### tracks transitive dependencies beyond one hop

1. dir create all
2. file write
3. graph analyze test
   - Expected: runner_list_contains(deps, "src/app/test_incremental_state_shared.spl") is true
   - Expected: runner_list_contains(deps, "src/app/test_dep_graph_shared.spl") is true
   - Expected: runner_list_contains(deps, "src/app/test_cache_shared.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dir_create_all(runner_dep_graph_spec_root)
val test_path = runner_dep_graph_test_path("sample_spec.spl")
file_write(test_path, "use app.test_runner_new.test_runner_main.{discover_tests}\n")

val graph = test_dep_graph_new()
graph.analyze_test(test_path)
val deps = graph.get_deps(test_path)

expect(runner_list_contains(deps, "src/app/test_incremental_state_shared.spl")).to_equal(true)
expect(runner_list_contains(deps, "src/app/test_dep_graph_shared.spl")).to_equal(true)
expect(runner_list_contains(deps, "src/app/test_cache_shared.spl")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_new/test_dep_graph_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TestRunner dependency graph

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
