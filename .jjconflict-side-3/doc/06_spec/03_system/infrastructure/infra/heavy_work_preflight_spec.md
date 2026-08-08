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
| 12 | 12 | 0 | 0 |

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

#### rejects overlapping native builds

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_file("scripts/check/check-heavy-work-preflight.shs")
expect(src.contains("No overlapping native builds")).to_equal(true)
expect(src.contains("MAX_ACTIVE_NATIVE_BUILDS")).to_equal(true)
expect(src.contains("NATIVE_BUILD_PROC_ROOT")).to_equal(true)
expect(src.contains("native_build_running=")).to_equal(true)
expect(src.contains("native_build_at_most_")).to_equal(true)
expect(src.contains("native_build_process_scan")).to_equal(true)
```

</details>

#### counts an exact native-build argv without counting its wrapper

<details>
<summary>Executable SSpec</summary>

```simple
val command = "root=$(mktemp -d); mkdir -p $root/1 $root/2; printf 'simple\\000native-build\\000' > $root/1/cmdline; printf 'timeout\\000simple\\000native-build\\000' > $root/2/cmdline; NATIVE_BUILD_PROC_ROOT=$root MAX_ACTIVE_NATIVE_BUILDS=0 sh scripts/check/check-heavy-work-preflight.shs; code=$?; rm -rf $root; exit $code"
val (stdout, _, code) = process_run("sh", ["-c", command])
expect(stdout).to_contain("INFO native_build_running=1")
expect(stdout).to_contain("FAIL native_build_at_most_0")
expect(code).to_equal(1)
```

</details>

#### fails closed when process inspection is unavailable

<details>
<summary>Executable SSpec</summary>

```simple
val missing_command = "NATIVE_BUILD_PROC_ROOT=/missing/simple-preflight-proc sh scripts/check/check-heavy-work-preflight.shs"
val (missing_stdout, _, missing_code) = process_run("sh", ["-c", missing_command])
expect(missing_stdout).to_contain("FAIL native_build_process_scan")
expect(missing_code).to_equal(1)

val unreadable_command = "root=$(mktemp -d); chmod 000 $root; NATIVE_BUILD_PROC_ROOT=$root sh scripts/check/check-heavy-work-preflight.shs; code=$?; chmod 700 $root; rmdir $root; exit $code"
val (unreadable_stdout, _, unreadable_code) = process_run("sh", ["-c", unreadable_command])
expect(unreadable_stdout).to_contain("FAIL native_build_process_scan")
expect(unreadable_code).to_equal(1)
```

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
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
