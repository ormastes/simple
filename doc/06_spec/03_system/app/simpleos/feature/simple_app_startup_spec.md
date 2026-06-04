# Simple App Startup Specification

> <details>

<!-- sdn-diagram:id=simple_app_startup_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_app_startup_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_app_startup_spec -> std
simple_app_startup_spec -> os
simple_app_startup_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_app_startup_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple App Startup Specification

## Scenarios

### SimpleOS app startup prefetch

### REQ-100: SimpleOS launch metadata

#### should plan SMF launch through SimpleOS VFS prewarm

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metadata = launch_metadata_for_simpleos_path("/sys/apps/simple.smf")
val plan = startup_plan_from_metadata("/sys/apps/simple.smf", [], metadata, false, true)
expect(plan.target_os).to_equal("simpleos")
expect(plan.entry_kind).to_equal("smf")
expect(plan.cache_strategy).to_equal("simpleos_vfs_prewarm")
expect(plan.include_mmap_cache).to_equal(true)
```

</details>

#### should plan native SimpleOS app launch without app arg parser

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metadata = launch_metadata_for_simpleos_path("/sys/apps/native_tool")
val plan = startup_plan_from_metadata("/sys/apps/native_tool", [], metadata, false, true)
expect(plan.target_os).to_equal("simpleos")
expect(plan.entry_kind).to_equal("native")
expect(plan.include_arg_parser).to_equal(false)
```

</details>

### REQ-101: WM hover prefetch

#### should prefetch cached executable bytes on hover without launching

1. launcher init

2. app registry load hardcoded fallback

3. app registry cache bytes
   - Expected: hit is true
   - Expected: launcher_prefetch_count() equals `1`
   - Expected: launcher_prefetch_last_path() equals `/sys/apps/simple.smf`
   - Expected: launcher_prefetch_last_cache_hit() is true
   - Expected: launcher_get_running_app_count() equals `0`
   - Expected: app_registry_cached_bytes("/sys/apps/simple").len() equals `3`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
app_registry_load_hardcoded_fallback()
app_registry_cache_bytes("/sys/apps/simple", [1u8, 2u8, 3u8])

val hit = launcher_hover_executable_icon("/sys/apps/simple.smf")

expect(hit).to_equal(true)
expect(launcher_prefetch_count()).to_equal(1)
expect(launcher_prefetch_last_path()).to_equal("/sys/apps/simple.smf")
expect(launcher_prefetch_last_cache_hit()).to_equal(true)
expect(launcher_get_running_app_count()).to_equal(0)
expect(app_registry_cached_bytes("/sys/apps/simple").len()).to_equal(3)
```

</details>

#### should record a miss for an executable that is not warmed yet

1. launcher init

2. app registry load hardcoded fallback
   - Expected: hit is false
   - Expected: launcher_prefetch_count() equals `1`
   - Expected: launcher_prefetch_last_path() equals `/sys/apps/editor.smf`
   - Expected: launcher_prefetch_last_cache_hit() is false
   - Expected: launcher_get_running_app_count() equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
app_registry_load_hardcoded_fallback()

val hit = launcher_hover_executable_icon("/sys/apps/editor.smf")

expect(hit).to_equal(false)
expect(launcher_prefetch_count()).to_equal(1)
expect(launcher_prefetch_last_path()).to_equal("/sys/apps/editor.smf")
expect(launcher_prefetch_last_cache_hit()).to_equal(false)
expect(launcher_get_running_app_count()).to_equal(0)
```

</details>

#### should reject empty hover paths without recording a prefetch

1. launcher init
   - Expected: hit is false
   - Expected: launcher_prefetch_count() equals `0`
   - Expected: launcher_prefetch_last_path() equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val hit = launcher_hover_executable_icon("")
expect(hit).to_equal(false)
expect(launcher_prefetch_count()).to_equal(0)
expect(launcher_prefetch_last_path()).to_equal("")
```

</details>

### REQ-102: launcher icon index prefetch

#### should prefetch the executable path for a seeded launcher icon

1. launcher init

2. app registry load hardcoded fallback

3. app registry cache bytes
   - Expected: hit is true
   - Expected: launcher_prefetch_count() equals `1`
   - Expected: launcher_prefetch_last_path() equals `/sys/apps/simple.smf`
   - Expected: launcher_get_running_app_count() equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
app_registry_load_hardcoded_fallback()
app_registry_cache_bytes("/sys/apps/simple", [9u8])

val hit = launcher_prefetch_app_index(11)

expect(hit).to_equal(true)
expect(launcher_prefetch_count()).to_equal(1)
expect(launcher_prefetch_last_path()).to_equal("/sys/apps/simple.smf")
expect(launcher_get_running_app_count()).to_equal(0)
```

</details>

#### should reject out-of-range icon indexes

1. launcher init
   - Expected: hit is false
   - Expected: launcher_prefetch_count() equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val hit = launcher_prefetch_app_index(999u64)
expect(hit).to_equal(false)
expect(launcher_prefetch_count()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simple_app_startup_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS app startup prefetch
- REQ-100: SimpleOS launch metadata
- REQ-101: WM hover prefetch
- REQ-102: launcher icon index prefetch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
