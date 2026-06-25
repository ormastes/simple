# Dashboard System Specification

> 1. verify

<!-- sdn-diagram:id=dashboard_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dashboard_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dashboard_system_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dashboard_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dashboard System Specification

## Scenarios

### Dashboard System Tests

#### collect generates dashboard tables and cache

1. verify
2. verify
3. verify
4. verify
5. verify
6. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["collect", "--mode=full"])
verify(result.exit_code == 0)
verify(result.stdout.contains("Collection complete."))

verify(file_exists("doc/10_metrics/dashboard/tables/todos.sdn"))
verify(file_exists("doc/10_metrics/dashboard/tables/test_status.sdn"))
verify(file_exists("doc/10_metrics/dashboard/dashboard_db.cache.sdn"))

val todos = file_read("doc/10_metrics/dashboard/tables/todos.sdn")
verify(todos.contains("todos |"))
```

</details>

#### status prints summary

1. verify
2. verify
3. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val result = run_simple(["status"])
verify(result.exit_code == 0)
verify(result.stdout.contains("Project Status Overview"))
verify(result.stdout.contains("Todos:"))
```

</details>

#### spipe summary prints suite/test counts

1. verify
2. verify
3. verify
4. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val result = run_simple(["spipe"])
verify(result.exit_code == 0)
verify(result.stdout.contains("SPipe Test Summary"))
verify(result.stdout.contains("Suites:"))
verify(result.stdout.contains("Tests:"))
```

</details>

#### export json includes summary and tables

1. verify
2. verify
3. verify
4. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val result = run_simple(["export", "--format=json"])
verify(result.exit_code == 0)
verify(result.stdout.contains("\"summary\""))
verify(result.stdout.contains("\"tables\""))
verify(result.stdout.contains("\"todos\""))
```

</details>

#### snapshot creates history file for today

1. verify
2. verify
3. file delete
4. verify
5. verify
6. verify
7. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val date = shell_output("date +%Y-%m-%d")
val month = shell_output("date +%Y-%m")
verify(date.len() > 0)
verify(month.len() > 0)

val snapshot_path = "doc/10_metrics/dashboard/history/{month}/{date}.sdn"
# Remove existing snapshot to ensure creation is exercised
if file_exists(snapshot_path):
    file_delete(snapshot_path)

val result = run_simple(["snapshot"])
verify(result.exit_code == 0)
verify(file_exists(snapshot_path))

val snapshot = file_read(snapshot_path)
verify(snapshot.contains("todos |"))
verify(snapshot.contains("features |"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/infrastructure/dashboard_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Dashboard System Tests

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
