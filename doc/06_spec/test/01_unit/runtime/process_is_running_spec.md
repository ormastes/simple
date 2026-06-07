# Process Is Running Specification

> 1. process wait

<!-- sdn-diagram:id=process_is_running_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=process_is_running_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

process_is_running_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=process_is_running_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Process Is Running Specification

## Scenarios

### rt_process_is_running with async-spawned children

#### reports async-spawned child as running while alive

1. process wait


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Spawn a child that sleeps for 5 seconds (long enough to check liveness)
val pid = process_spawn_async("sleep", ["5"])
expect(pid > 0).to_be_true()

# Child should be running immediately after spawn
val running = process_is_running(pid)
expect(running).to_be_true()

# Clean up: kill child and reap it
process_wait(pid, 100)
```

</details>

#### reports async-spawned child as not running after it exits

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Spawn a child that exits immediately
val pid = process_spawn_async("true", [])
expect(pid > 0).to_be_true()

# Wait for the child to finish
val exit_code = process_wait(pid, 2000)
expect(exit_code >= 0).to_be_true()

# After waitpid, process should not be running
val running = process_is_running(pid)
expect(running).to_be_false()
```

</details>

#### returns false for invalid pid zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val running = process_is_running(0)
expect(running).to_be_false()
```

</details>

#### returns false for negative pid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val running = process_is_running(-1)
expect(running).to_be_false()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/01_unit/runtime/process_is_running_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- rt_process_is_running with async-spawned children

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
