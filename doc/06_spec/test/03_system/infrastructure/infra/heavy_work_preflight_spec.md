# Heavy Work Preflight Specification

> <details>

<!-- sdn-diagram:id=heavy_work_preflight_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=heavy_work_preflight_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

heavy_work_preflight_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=heavy_work_preflight_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Heavy Work Preflight Specification

## Scenarios

### heavy work preflight script

#### script exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists("scripts/check/check-heavy-work-preflight.shs")).to_equal(true)
```

</details>

#### checks disk space

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_file("scripts/check/check-heavy-work-preflight.shs")
expect(src.contains("Disk space")).to_equal(true)
expect(src.contains("disk_space_min_")).to_equal(true)
expect(src.contains("MIN_DISK_GIB")).to_equal(true)
```

</details>

#### checks available memory

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_file("scripts/check/check-heavy-work-preflight.shs")
expect(src.contains("Available memory")).to_equal(true)
expect(src.contains("memory_min_")).to_equal(true)
expect(src.contains("MIN_MEM_GIB")).to_equal(true)
```

</details>

#### checks swap overcommit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_file("scripts/check/check-heavy-work-preflight.shs")
expect(src.contains("Swap not over-committed")).to_equal(true)
expect(src.contains("swap_not_overcommitted")).to_equal(true)
```

</details>

<details>
<summary>Advanced: checks cpu headroom</summary>

#### checks cpu headroom

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_file("scripts/check/check-heavy-work-preflight.shs")
expect(src.contains("CPU headroom")).to_equal(true)
expect(src.contains("cpu_load_below_half")).to_equal(true)
```

</details>


</details>

#### checks qemu guest count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_file("scripts/check/check-heavy-work-preflight.shs")
expect(src.contains("No active QEMU guests")).to_equal(true)
expect(src.contains("qemu_at_most_one")).to_equal(true)
```

</details>

#### checks kernel log for danger patterns

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_file("scripts/check/check-heavy-work-preflight.shs")
expect(src.contains("Kernel log")).to_equal(true)
expect(src.contains("hard LOCKUP")).to_equal(true)
expect(src.contains("Out of memory")).to_equal(true)
```

</details>

#### checks git working tree and lock files

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_file("scripts/check/check-heavy-work-preflight.shs")
expect(src.contains("Git working tree clean")).to_equal(true)
expect(src.contains("No stale lock files")).to_equal(true)
expect(src.contains("index.lock")).to_equal(true)
```

</details>

#### reports preflight summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_file("scripts/check/check-heavy-work-preflight.shs")
expect(src.contains("preflight=READY")).to_equal(true)
expect(src.contains("preflight=BLOCKED")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/infrastructure/infra/heavy_work_preflight_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- heavy work preflight script

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
