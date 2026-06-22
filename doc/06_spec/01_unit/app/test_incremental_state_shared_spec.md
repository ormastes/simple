# Test Incremental State Shared Specification

> 1. dir create all

<!-- sdn-diagram:id=test_incremental_state_shared_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_incremental_state_shared_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_incremental_state_shared_spec -> std
test_incremental_state_shared_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_incremental_state_shared_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Incremental State Shared Specification

## Scenarios

### IncrementalTestState

#### records and reloads runner cache entries without persisting a dep graph file

1. dir create all
2. file write
3. state record runner result
4. state save
   - Expected: entry.result_status equals `0`
   - Expected: entry.result_passed equals `3`
   - Expected: entry.result_skipped equals `1`
   - Expected: file_exists(graph_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dir_create_all(incremental_state_spec_root)
val test_path = incremental_state_test_path("sample_spec.spl")
val cache_path = incremental_state_test_path("cache.sdn")
val graph_path = incremental_state_test_path("graph.sdn")
file_write(test_path, "use app.test_runner_new.test_runner_main.{discover_tests}\n")

val state = incremental_test_state_new(cache_path, "", false)
state.record_runner_result(test_path, 3, 0, 1, 42)
state.save()

val reloaded = incremental_test_state_load(cache_path, "", false)
val entry = reloaded.check_freshness(test_path)

expect(entry.result_status).to_equal(0)
expect(entry.result_passed).to_equal(3)
expect(entry.result_skipped).to_equal(1)
expect(file_exists(graph_path)).to_equal(false)
```

</details>

#### uses the shared dep graph in runner mode without reverse dependency tracking

1. dir create all
2. file write
   - Expected: entry.result_status equals `-1`
   - Expected: incremental_list_contains(deps, "src/app/test_dep_graph_shared.spl") is true
   - Expected: state.get_affected_tests("src/app/test_dep_graph_shared.spl").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dir_create_all(incremental_state_spec_root)
val test_path = incremental_state_test_path("sample_spec.spl")
file_write(test_path, "use app.test_runner_new.test_runner_main.{discover_tests}\n")

val state = incremental_test_state_new(incremental_state_test_path("cache.sdn"), "", false)
val entry = state.check_freshness(test_path)
val deps = state.get_deps(test_path)

expect(entry.result_status).to_equal(-1)
expect(incremental_list_contains(deps, "src/app/test_dep_graph_shared.spl")).to_equal(true)
expect(state.get_affected_tests("src/app/test_dep_graph_shared.spl").len()).to_equal(0)
```

</details>

#### persists reverse dependencies in daemon mode

1. dir create all
2. file write
3. incremental state test path
4. incremental state test path
5. state check freshness
6. state save
7. incremental state test path
8. incremental state test path
   - Expected: incremental_list_contains(reloaded.get_affected_tests("src/app/test_incremental_state_shared.spl"), test_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dir_create_all(incremental_state_spec_root)
val test_path = incremental_state_test_path("sample_spec.spl")
file_write(test_path, "use app.test_daemon.daemon.{TestDaemon}\n")

val state = incremental_test_state_new(
    incremental_state_test_path("cache.sdn"),
    incremental_state_test_path("graph.sdn"),
    true
)
state.check_freshness(test_path)
state.save()

val reloaded = incremental_test_state_load(
    incremental_state_test_path("cache.sdn"),
    incremental_state_test_path("graph.sdn"),
    true
)

expect(incremental_list_contains(reloaded.get_affected_tests("src/app/test_incremental_state_shared.spl"), test_path)).to_equal(true)
```

</details>

#### records and reloads daemon cache output with reverse dependency tracking

1. dir create all
2. file write
3. state record daemon result
4. state save
   - Expected: entry.result_status equals `2`
   - Expected: entry.result_output equals `line one\nline two`
   - Expected: incremental_list_contains(reloaded.get_affected_tests("src/app/test_incremental_state_shared.spl"), test_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dir_create_all(incremental_state_spec_root)
val test_path = incremental_state_test_path("sample_spec.spl")
val cache_path = incremental_state_test_path("cache.sdn")
val graph_path = incremental_state_test_path("graph.sdn")
file_write(test_path, "use app.test_daemon.daemon.{TestDaemon}\n")

val state = incremental_test_state_new(cache_path, graph_path, true)
state.record_daemon_result(test_path, 2, 1, 0, 0, 15, "line one\nline two")
state.save()

val reloaded = incremental_test_state_load(cache_path, graph_path, true)
val entry = reloaded.check_freshness(test_path)

expect(entry.result_status).to_equal(2)
expect(entry.result_output).to_equal("line one\nline two")
expect(incremental_list_contains(reloaded.get_affected_tests("src/app/test_incremental_state_shared.spl"), test_path)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_incremental_state_shared_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- IncrementalTestState

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
