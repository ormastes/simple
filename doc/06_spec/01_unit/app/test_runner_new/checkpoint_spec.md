# Checkpoint Specification

> <details>

<!-- sdn-diagram:id=checkpoint_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=checkpoint_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

checkpoint_spec -> std
checkpoint_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=checkpoint_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Checkpoint Specification

## Scenarios

### Checkpoint struct

#### should create checkpoint with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ckpt = Checkpoint(
    timestamp_ms: 1739530800000,
    completed_files: ["test1.spl", "test2.spl"],
    total_passed: 10,
    total_failed: 2,
    total_skipped: 3,
    shutdown_reason: "memory"
)

expect(ckpt.timestamp_ms).to_equal(1739530800000)
expect(ckpt.completed_files.len()).to_equal(2)
expect(ckpt.total_passed).to_equal(10)
expect(ckpt.total_failed).to_equal(2)
expect(ckpt.total_skipped).to_equal(3)
expect(ckpt.shutdown_reason).to_equal("memory")
```

</details>

### make_empty_checkpoint

#### should create empty checkpoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ckpt = make_empty_checkpoint()

expect(ckpt.timestamp_ms).to_equal(0)
expect(ckpt.completed_files.len()).to_equal(0)
expect(ckpt.total_passed).to_equal(0)
expect(ckpt.total_failed).to_equal(0)
expect(ckpt.total_skipped).to_equal(0)
expect(ckpt.shutdown_reason).to_equal("")
```

</details>

### checkpoint_save and load

#### should save checkpoint to file

1. checkpoint save
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val completed = ["test/unit/a.spl", "test/unit/b.spl"]
checkpoint_save(completed, 5, 1, 2, "cpu")

val exists = file_exists(".simple-test-checkpoint.sdn")
expect(exists).to_equal(true)
```

</details>

#### should save valid SDN format

1. checkpoint save
   - Expected: content contains `checkpoint {`
   - Expected: content contains `timestamp_ms`
   - Expected: content contains `completed_files`
   - Expected: content contains `total_passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val completed = ["file1.spl"]
checkpoint_save(completed, 10, 0, 0, "periodic")

val content = file_read(".simple-test-checkpoint.sdn")

# Check for expected SDN structure
expect(content.contains("checkpoint {")).to_equal(true)
expect(content.contains("timestamp_ms")).to_equal(true)
expect(content.contains("completed_files")).to_equal(true)
expect(content.contains("total_passed")).to_equal(true)
```

</details>

#### should load saved checkpoint

1. checkpoint save
   - Expected: loaded.completed_files.len() equals `2`
   - Expected: loaded.completed_files[0] equals `test/unit/x.spl`
   - Expected: loaded.completed_files[1] equals `test/unit/y.spl`
   - Expected: loaded.total_passed equals `15`
   - Expected: loaded.total_failed equals `3`
   - Expected: loaded.total_skipped equals `5`
   - Expected: loaded.shutdown_reason equals `memory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val completed = ["test/unit/x.spl", "test/unit/y.spl"]
checkpoint_save(completed, 15, 3, 5, "memory")

val loaded = checkpoint_load()

expect(loaded.completed_files.len()).to_equal(2)
expect(loaded.completed_files[0]).to_equal("test/unit/x.spl")
expect(loaded.completed_files[1]).to_equal("test/unit/y.spl")
expect(loaded.total_passed).to_equal(15)
expect(loaded.total_failed).to_equal(3)
expect(loaded.total_skipped).to_equal(5)
expect(loaded.shutdown_reason).to_equal("memory")
```

</details>

### checkpoint_skip_completed

#### should return all files when checkpoint empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all_files = ["a.spl", "b.spl", "c.spl"]
val ckpt = make_empty_checkpoint()

val remaining = checkpoint_skip_completed(all_files, ckpt)

expect(remaining.len()).to_equal(3)
```

</details>

#### should filter out completed files

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all_files = ["test/a.spl", "test/b.spl", "test/c.spl", "test/d.spl"]
val ckpt = Checkpoint(
    timestamp_ms: 0,
    completed_files: ["test/a.spl", "test/c.spl"],
    total_passed: 0,
    total_failed: 0,
    total_skipped: 0,
    shutdown_reason: ""
)

val remaining = checkpoint_skip_completed(all_files, ckpt)

expect(remaining.len()).to_equal(2)
expect(remaining[0]).to_equal("test/b.spl")
expect(remaining[1]).to_equal("test/d.spl")
```

</details>

#### should return empty when all completed

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all_files = ["x.spl", "y.spl"]
val ckpt = Checkpoint(
    timestamp_ms: 0,
    completed_files: ["x.spl", "y.spl"],
    total_passed: 0,
    total_failed: 0,
    total_skipped: 0,
    shutdown_reason: ""
)

val remaining = checkpoint_skip_completed(all_files, ckpt)

expect(remaining.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_new/checkpoint_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Checkpoint struct
- make_empty_checkpoint
- checkpoint_save and load
- checkpoint_skip_completed

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
