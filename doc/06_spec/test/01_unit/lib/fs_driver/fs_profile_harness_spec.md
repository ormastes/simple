# Fs Profile Harness Specification

> <details>

<!-- sdn-diagram:id=fs_profile_harness_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fs_profile_harness_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fs_profile_harness_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fs_profile_harness_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fs Profile Harness Specification

## Scenarios

### fs_bench_harness

### time_function

#### AC-1: returns elapsed microseconds greater than zero for RamFS open

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elapsed = time_function("ramfs_open")
expect elapsed > 0
```

</details>

#### AC-1: returns elapsed microseconds within reasonable range for RamFS open

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elapsed = time_function("ramfs_open")
expect elapsed < 1000000
```

</details>

#### AC-1: returns elapsed microseconds greater than zero for RamFS stat

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elapsed = time_function("ramfs_stat")
expect elapsed > 0
```

</details>

#### AC-1: returns elapsed microseconds within reasonable range for RamFS stat

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elapsed = time_function("ramfs_stat")
expect elapsed < 1000000
```

</details>

#### AC-1: returns elapsed microseconds greater than zero for RamFS close

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elapsed = time_function("ramfs_close")
expect elapsed > 0
```

</details>

#### AC-1: returns elapsed microseconds within reasonable range for RamFS close

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elapsed = time_function("ramfs_close")
expect elapsed < 1000000
```

</details>

#### AC-1: returns elapsed microseconds greater than zero for FAT32 parse

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elapsed = time_function("fat32_parse_superblock")
expect elapsed > 0
```

</details>

#### AC-1: returns elapsed microseconds within reasonable range for FAT32 parse

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elapsed = time_function("fat32_parse_superblock")
expect elapsed < 1000000
```

</details>

#### AC-1: returns elapsed microseconds greater than zero for FAT32 fat_search_long

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elapsed = time_function("fat32_fat_search_long")
expect elapsed > 0
```

</details>

#### AC-1: returns elapsed microseconds within reasonable range for FAT32 fat_search_long

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elapsed = time_function("fat32_fat_search_long")
expect elapsed < 1000000
```

</details>

### create_benchmark_suite

#### AC-1: creates a suite with a non-empty name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val suite = create_benchmark_suite("ramfs_suite")
expect suite.name == "ramfs_suite"
```

</details>

#### AC-1: new suite has zero recorded timings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val suite = create_benchmark_suite("empty_suite")
expect suite.count == 0
```

</details>

### add_benchmark

#### AC-1: adds a timing entry and increments count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val suite = create_benchmark_suite("test_suite")
val suite2 = add_benchmark(suite, "ramfs_open", 42)
expect suite2.count == 1
```

</details>

#### AC-1: recorded timing value matches inserted value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val suite = create_benchmark_suite("test_suite")
val suite2 = add_benchmark(suite, "ramfs_open", 99)
expect suite2.last_timing == 99
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/fs_driver/fs_profile_harness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- fs_bench_harness
- time_function
- create_benchmark_suite
- add_benchmark

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
