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
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Dep Graph Specification

## Scenarios

### TestDaemon dependency graph

#### tracks transitive dependencies beyond one hop

1. dir create all
2. file write
3. graph analyze test
   - Expected: daemon_list_contains(deps, "src/app/test_incremental_state_shared.spl") is true
   - Expected: daemon_list_contains(deps, "src/app/test_dep_graph_shared.spl") is true
   - Expected: daemon_list_contains(deps, "src/app/test_cache_shared.spl") is true
   - Expected: daemon_list_contains(graph.get_affected_tests("src/app/test_incremental_state_shared.spl"), test_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dir_create_all(daemon_dep_graph_spec_root)
val test_path = daemon_dep_graph_test_path("sample_spec.spl")
file_write(test_path, "use app.test_daemon.daemon.{TestDaemon}\n")

val graph = test_dep_graph_new(daemon_dep_graph_test_path("graph.sdn"))
graph.analyze_test(test_path)
val deps = graph.get_deps(test_path)

expect(daemon_list_contains(deps, "src/app/test_incremental_state_shared.spl")).to_equal(true)
expect(daemon_list_contains(deps, "src/app/test_dep_graph_shared.spl")).to_equal(true)
expect(daemon_list_contains(deps, "src/app/test_cache_shared.spl")).to_equal(true)
expect(daemon_list_contains(graph.get_affected_tests("src/app/test_incremental_state_shared.spl"), test_path)).to_equal(true)
```

</details>

#### clears stale reverse dependencies when a test file becomes empty

1. dir create all
2. file write
3. graph analyze test
   - Expected: daemon_list_contains(graph.get_affected_tests("src/app/test_daemon/cache.spl"), test_path) is true
4. file write
5. graph analyze test
   - Expected: graph.get_deps(test_path).len() equals `0`
   - Expected: daemon_list_contains(graph.get_affected_tests("src/app/test_daemon/cache.spl"), test_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dir_create_all(daemon_dep_graph_spec_root)
val test_path = daemon_dep_graph_test_path("sample_spec.spl")
file_write(test_path, "use app.test_daemon.cache.{test_result_cache_new}\n")

val graph = test_dep_graph_new(daemon_dep_graph_test_path("graph.sdn"))
graph.analyze_test(test_path)
expect(daemon_list_contains(graph.get_affected_tests("src/app/test_daemon/cache.spl"), test_path)).to_equal(true)

file_write(test_path, "")
graph.analyze_test(test_path)

expect(graph.get_deps(test_path).len()).to_equal(0)
expect(daemon_list_contains(graph.get_affected_tests("src/app/test_daemon/cache.spl"), test_path)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_daemon/test_dep_graph_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TestDaemon dependency graph

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
