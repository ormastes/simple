# Async Spawn Analysis Specification

> <details>

<!-- sdn-diagram:id=async_spawn_analysis_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_spawn_analysis_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_spawn_analysis_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_spawn_analysis_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Spawn Analysis Specification

## Scenarios

### is_in_list utility

#### finds existing name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_in_list("main", ["main", "setup", "init"])).to_equal(true)
```

</details>

#### returns false for missing name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_in_list("handler", ["main", "setup"])).to_equal(false)
```

</details>

#### returns false for empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_in_list("main", [])).to_equal(false)
```

</details>

### get_boot_spawn_count lookup

#### returns count for existing task

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = ["uart_rx", "spi_tx"]
val counts = [3, 2]
expect(get_boot_spawn_count("uart_rx", names, counts)).to_equal(3)
expect(get_boot_spawn_count("spi_tx", names, counts)).to_equal(2)
```

</details>

#### returns zero for unknown task

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = ["uart_rx"]
val counts = [3]
expect(get_boot_spawn_count("unknown", names, counts)).to_equal(0)
```

</details>

#### returns zero for empty arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(get_boot_spawn_count("any", [], [])).to_equal(0)
```

</details>

### Init phase validation

#### passes when all spawns in init-reachable

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sa = make_clean_analysis()
val result = verify_spawn_bounds(sa)
expect(result.has_errors).to_equal(false)
expect(result.total_spawns).to_equal(2)
```

</details>

#### errors when spawn outside init-reachable

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sa = make_analysis_with_outside_spawn()
val result = verify_spawn_bounds(sa)
expect(result.has_errors).to_equal(true)
var found_outside = false
for diag in result.diagnostics:
    if diag.message.contains("outside init phase"):
        found_outside = true
expect(found_outside).to_equal(true)
```

</details>

#### errors when spawn after await

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sa = make_analysis_with_after_await()
val result = verify_spawn_bounds(sa)
expect(result.has_errors).to_equal(true)
var found_after = false
for diag in result.diagnostics:
    if diag.message.contains("after await"):
        found_after = true
expect(found_after).to_equal(true)
```

</details>

### Instance limits

#### passes when spawns within instance count

1. spawn sites: [make spawn site
2. task infos: [make task info
   - Expected: result.has_errors is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sa = SpawnAnalysis(
    init_functions: ["main"],
    init_reachable: ["main"],
    spawn_sites: [make_spawn_site("uart_rx", "main", false)],
    task_infos: [make_task_info("uart_rx", 4)],
    group_infos: [],
    boot_spawn_names: ["uart_rx"],
    boot_spawn_counts: [2]
)
val result = verify_spawn_bounds(sa)
expect(result.has_errors).to_equal(false)
```

</details>

#### passes when spawns equal instance count

1. spawn sites: [make spawn site
2. task infos: [make task info
   - Expected: result.has_errors is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sa = SpawnAnalysis(
    init_functions: ["main"],
    init_reachable: ["main"],
    spawn_sites: [make_spawn_site("uart_rx", "main", false)],
    task_infos: [make_task_info("uart_rx", 3)],
    group_infos: [],
    boot_spawn_names: ["uart_rx"],
    boot_spawn_counts: [3]
)
val result = verify_spawn_bounds(sa)
expect(result.has_errors).to_equal(false)
```

</details>

#### errors when spawns exceed instance count

1. spawn sites: [make spawn site
2. task infos: [make task info
   - Expected: result.has_errors is true
   - Expected: found_instance_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sa = SpawnAnalysis(
    init_functions: ["main"],
    init_reachable: ["main"],
    spawn_sites: [make_spawn_site("uart_rx", "main", false)],
    task_infos: [make_task_info("uart_rx", 2)],
    group_infos: [],
    boot_spawn_names: ["uart_rx"],
    boot_spawn_counts: [5]
)
val result = verify_spawn_bounds(sa)
expect(result.has_errors).to_equal(true)
var found_instance_error = false
for diag in result.diagnostics:
    if diag.message.contains("spawned 5 times") and diag.message.contains("instances=2"):
        found_instance_error = true
expect(found_instance_error).to_equal(true)
```

</details>

### Group capacity

#### passes when group total within cap

1. make spawn site
2. make spawn site
3. make task info grouped
4. make task info grouped
5. group infos: [make group
   - Expected: result.has_errors is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sa = SpawnAnalysis(
    init_functions: ["main"],
    init_reachable: ["main"],
    spawn_sites: [
        make_spawn_site("uart_rx", "main", false),
        make_spawn_site("spi_tx", "main", false)
    ],
    task_infos: [
        make_task_info_grouped("uart_rx", 4, "io_pool"),
        make_task_info_grouped("spi_tx", 4, "io_pool")
    ],
    group_infos: [make_group("io_pool", 6, ["uart_rx", "spi_tx"])],
    boot_spawn_names: ["uart_rx", "spi_tx"],
    boot_spawn_counts: [2, 3]
)
val result = verify_spawn_bounds(sa)
# Grouped tasks skip individual instance check (group != nil)
# Group total 2+3=5 <= 6 cap
expect(result.has_errors).to_equal(false)
```

</details>

#### errors when group total exceeds cap

1. make spawn site
2. make spawn site
3. make task info grouped
4. make task info grouped
5. group infos: [make group
   - Expected: result.has_errors is true
   - Expected: found_group_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sa = SpawnAnalysis(
    init_functions: ["main"],
    init_reachable: ["main"],
    spawn_sites: [
        make_spawn_site("uart_rx", "main", false),
        make_spawn_site("spi_tx", "main", false)
    ],
    task_infos: [
        make_task_info_grouped("uart_rx", 10, "io_pool"),
        make_task_info_grouped("spi_tx", 10, "io_pool")
    ],
    group_infos: [make_group("io_pool", 4, ["uart_rx", "spi_tx"])],
    boot_spawn_names: ["uart_rx", "spi_tx"],
    boot_spawn_counts: [3, 3]
)
val result = verify_spawn_bounds(sa)
expect(result.has_errors).to_equal(true)
var found_group_error = false
for diag in result.diagnostics:
    if diag.message.contains("task group") and diag.message.contains("cap=4"):
        found_group_error = true
expect(found_group_error).to_equal(true)
```

</details>

### Combined checks

#### reports multiple errors at once

1. make spawn site
2. make spawn site
3. make task info
4. make task info
   - Expected: result.has_errors is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sa = SpawnAnalysis(
    init_functions: ["main"],
    init_reachable: ["main"],
    spawn_sites: [
        make_spawn_site("uart_rx", "main", true),
        make_spawn_site("spi_tx", "handler", false)
    ],
    task_infos: [
        make_task_info("uart_rx", 1),
        make_task_info("spi_tx", 1)
    ],
    group_infos: [],
    boot_spawn_names: ["uart_rx"],
    boot_spawn_counts: [1]
)
val result = verify_spawn_bounds(sa)
expect(result.has_errors).to_equal(true)
# Should have at least 2 errors: after-await + outside init
expect(result.diagnostics.len()).to_be_greater_than(1)
```

</details>

#### passes clean module with no issues

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sa = make_clean_analysis()
val result = verify_spawn_bounds(sa)
expect(result.has_errors).to_equal(false)
expect(result.diagnostics.len()).to_equal(0)
expect(result.total_spawns).to_equal(2)
```

</details>

### Data structure construction

#### creates SpawnSite correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val site = make_spawn_site("uart_rx", "main", false)
expect(site.task_name).to_equal("uart_rx")
expect(site.caller_name).to_equal("main")
expect(site.is_after_await).to_equal(false)
```

</details>

#### creates TaskInfo correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = make_task_info("uart_rx", 4)
expect(info.name).to_equal("uart_rx")
expect(info.instances).to_equal(4)
expect(info.group).to_be_nil()
```

</details>

#### creates TaskGroupInfo correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val group = make_group("io_pool", 8, ["uart_rx", "spi_tx"])
expect(group.name).to_equal("io_pool")
expect(group.cap).to_equal(8)
expect(group.members.len()).to_equal(2)
```

</details>

#### creates SpawnAnalysis correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sa = make_clean_analysis()
expect(sa.init_functions.len()).to_equal(1)
expect(sa.init_reachable.len()).to_equal(2)
expect(sa.spawn_sites.len()).to_equal(2)
expect(sa.task_infos.len()).to_equal(2)
expect(sa.boot_spawn_names.len()).to_equal(2)
expect(sa.boot_spawn_counts.len()).to_equal(2)
```

</details>

### compute_init_reachable

#### includes init functions themselves

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reachable = compute_init_reachable(["main"], [], [])
expect(is_in_list("main", reachable)).to_equal(true)
```

</details>

#### follows direct calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val callers = ["main", "main"]
val callees = ["setup", "init_hw"]
val reachable = compute_init_reachable(["main"], callers, callees)
expect(is_in_list("main", reachable)).to_equal(true)
expect(is_in_list("setup", reachable)).to_equal(true)
expect(is_in_list("init_hw", reachable)).to_equal(true)
```

</details>

#### follows transitive calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val callers = ["main", "setup"]
val callees = ["setup", "init_hw"]
val reachable = compute_init_reachable(["main"], callers, callees)
expect(is_in_list("init_hw", reachable)).to_equal(true)
```

</details>

#### excludes unreachable functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val callers = ["main", "handler"]
val callees = ["setup", "process"]
val reachable = compute_init_reachable(["main"], callers, callees)
expect(is_in_list("setup", reachable)).to_equal(true)
expect(is_in_list("handler", reachable)).to_equal(false)
expect(is_in_list("process", reachable)).to_equal(false)
```

</details>

### Spawn analysis formatting

#### produces non-empty report

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sa = make_clean_analysis()
val report = format_spawn_analysis(sa)
expect(report.len()).to_be_greater_than(0)
expect(report).to_contain("Spawn Analysis:")
expect(report).to_contain("Init functions:")
expect(report).to_contain("Spawn sites:")
```

</details>

#### formats verification result

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sa = make_clean_analysis()
val result = verify_spawn_bounds(sa)
val output = format_spawn_verify_result(result)
expect(output).to_contain("Spawn Verification:")
expect(output).to_contain("All spawn checks passed.")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/async/async_spawn_analysis_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- is_in_list utility
- get_boot_spawn_count lookup
- Init phase validation
- Instance limits
- Group capacity
- Combined checks
- Data structure construction
- compute_init_reachable
- Spawn analysis formatting

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
