# Replay Checkpoint Types Specification

> <details>

<!-- sdn-diagram:id=replay_checkpoint_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_checkpoint_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_checkpoint_types_spec -> std
replay_checkpoint_types_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_checkpoint_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Checkpoint Types Specification

## Scenarios

### FdKind to_i32

#### File to_i32 returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FdKind.File
expect(f.to_i32()).to_equal(0)
```

</details>

#### Pipe to_i32 returns 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = FdKind.Pipe
expect(p.to_i32()).to_equal(1)
```

</details>

#### Socket to_i32 returns 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = FdKind.Socket
expect(p.to_i32()).to_equal(2)
```

</details>

### ProcessSnapshot create

#### create sets task_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ps = ProcessSnapshot.create(10, 0)
expect(ps.task_id).to_equal(10)
```

</details>

#### create sets parent_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ps = ProcessSnapshot.create(10, 5)
expect(ps.parent_id).to_equal(5)
```

</details>

#### create starts with empty fd_table

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ps = ProcessSnapshot.create(1, 0)
expect(ps.fd_table.len()).to_equal(0)
```

</details>

### ContainerCheckpoint create

#### create stores container_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cp = ContainerCheckpoint.create("ctr-001", 1)
expect(cp.container_id).to_equal("ctr-001")
```

</details>

#### create stores checkpoint_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cp = ContainerCheckpoint.create("ctr-001", 7)
expect(cp.checkpoint_id).to_equal(7)
```

</details>

#### process_count starts at 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cp = ContainerCheckpoint.create("ctr-x", 0)
expect(cp.process_count()).to_equal(0)
```

</details>

#### add_process increments process_count

1. cp add process
   - Expected: cp.process_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cp = ContainerCheckpoint.create("ctr-y", 2)
val ps = ProcessSnapshot.create(99, 0)
cp.add_process(ps)
expect(cp.process_count()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_checkpoint_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FdKind to_i32
- ProcessSnapshot create
- ContainerCheckpoint create

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
