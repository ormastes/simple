# ProcfsService Specification (G7)

> Process filesystem capsule backed by ECS. Validates initial state, PM endpoint mounting, node registration, path lookup (hit and miss), node count, and the canonical /proc path constant.

<!-- sdn-diagram:id=procfs_service_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=procfs_service_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

procfs_service_spec -> std
procfs_service_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=procfs_service_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ProcfsService Specification (G7)

Process filesystem capsule backed by ECS. Validates initial state, PM endpoint mounting, node registration, path lookup (hit and miss), node count, and the canonical /proc path constant.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #G7 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/os/services/procfs_service_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Process filesystem capsule backed by ECS. Validates initial state,
PM endpoint mounting, node registration, path lookup (hit and miss),
node count, and the canonical /proc path constant.

## Scenarios

### ProcfsService initial state

#### constructs with zero registered nodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = ProcfsService.new()
expect(svc.procfs_node_count()).to_equal(0)
```

</details>

#### PROC_FILE constant equals 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(PROC_FILE).to_equal(0)
```

</details>

#### PROC_DIR constant equals 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(PROC_DIR).to_equal(1)
```

</details>

#### procfs_list_pids_path returns /proc

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = ProcfsService.new()
expect(svc.procfs_list_pids_path()).to_equal("/proc")
```

</details>

### ProcfsService procfs_mount

#### mount stores pm_endpoint on service

1. var svc = ProcfsService new
2. svc procfs mount
   - Expected: svc.pm_endpoint equals `7777`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = ProcfsService.new()
svc.procfs_mount(7777)
expect(svc.pm_endpoint).to_equal(7777)
```

</details>

#### mount does not create any ECS nodes

1. var svc = ProcfsService new
2. svc procfs mount
   - Expected: svc.procfs_node_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = ProcfsService.new()
svc.procfs_mount(8888)
expect(svc.procfs_node_count()).to_equal(0)
```

</details>

### ProcfsService procfs_node_register

#### register increments node count

1. var svc = ProcfsService new
   - Expected: svc.procfs_node_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = ProcfsService.new()
val _e = svc.procfs_node_register("/proc/1", 1, PROC_DIR)
expect(svc.procfs_node_count()).to_equal(1)
```

</details>

#### register returns entity with positive id

1. var svc = ProcfsService new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = ProcfsService.new()
val e = svc.procfs_node_register("/proc/1/status", 1, PROC_FILE)
expect(e.id).to_be_greater_than(0)
```

</details>

### ProcfsService procfs_node_lookup

#### lookup registered node returns its source pid

1. var svc = ProcfsService new
   - Expected: pid equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = ProcfsService.new()
val _e = svc.procfs_node_register("/proc/42/cmdline", 42, PROC_FILE)
val pid = svc.procfs_node_lookup("/proc/42/cmdline")
expect(pid).to_equal(42)
```

</details>

#### lookup missing path returns -2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = ProcfsService.new()
val pid = svc.procfs_node_lookup("/proc/9999/status")
expect(pid).to_equal(-2)
```

</details>

#### lookup different path does not match registered node

1. var svc = ProcfsService new
   - Expected: pid equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = ProcfsService.new()
val _e = svc.procfs_node_register("/proc/1/maps", 1, PROC_FILE)
val pid = svc.procfs_node_lookup("/proc/1/status")
expect(pid).to_equal(-2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
