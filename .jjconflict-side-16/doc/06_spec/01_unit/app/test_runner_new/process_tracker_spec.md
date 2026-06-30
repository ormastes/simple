# Process Tracker Specification

> 1. tracker register pid

<!-- sdn-diagram:id=process_tracker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=process_tracker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

process_tracker_spec -> std
process_tracker_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=process_tracker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Process Tracker Specification

## Scenarios

### Process Tracker

#### tracks pid registration and unregister

1. tracker register pid
2. tracker register pid
   - Expected: tracker_get_pids().len() equals `2`
3. tracker unregister pid
   - Expected: pids.len() equals `1`
   - Expected: pids[0] equals `202`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
tracker_register_pid(101)
tracker_register_pid(202)

expect(tracker_get_pids().len()).to_equal(2)

tracker_unregister_pid(101)
val pids = tracker_get_pids()
expect(pids.len()).to_equal(1)
expect(pids[0]).to_equal(202)
```

</details>

#### tracks container registration and unregister

1. tracker register container
2. tracker register container
   - Expected: tracker_get_containers().len() equals `2`
3. tracker unregister container
   - Expected: containers.len() equals `1`
   - Expected: containers[0] equals `ctr-b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
tracker_register_container("ctr-a")
tracker_register_container("ctr-b")

expect(tracker_get_containers().len()).to_equal(2)

tracker_unregister_container("ctr-a")
val containers = tracker_get_containers()
expect(containers.len()).to_equal(1)
expect(containers[0]).to_equal("ctr-b")
```

</details>

#### clears tracked state and handles empty cleanup

1. tracker register pid
2. tracker register container
3. tracker clear
   - Expected: tracker_get_pids().len() equals `0`
   - Expected: tracker_get_containers().len() equals `0`
   - Expected: tracker_kill_all_children() equals `0`
   - Expected: tracker_stop_all_containers() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
tracker_register_pid(303)
tracker_register_container("ctr-c")
tracker_clear()

expect(tracker_get_pids().len()).to_equal(0)
expect(tracker_get_containers().len()).to_equal(0)
expect(tracker_kill_all_children()).to_equal(0)
expect(tracker_stop_all_containers()).to_equal(0)
```

</details>

#### exposes safe runtime probes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val docker_available = is_docker_available()
val containers = get_running_containers()

expect(docker_available == true or docker_available == false).to_equal(true)
expect(containers.len() >= 0).to_equal(true)
expect(tracker_check_heartbeat_alive(1000)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_new/process_tracker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Process Tracker

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
