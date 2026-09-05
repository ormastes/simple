# Simple App Startup Specification

> Tests covering SimpleOS app startup prefetch, REQ-100: SimpleOS launch metadata, REQ-101: WM hover prefetch, REQ-102: launcher icon index prefetch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple App Startup Specification

## Scenarios

### SimpleOS app startup prefetch

### REQ-100: SimpleOS launch metadata

#### keeps hosted executable launch filesystem-backed and bare-metal GOT explicit

- keeps hosted executable launch filesystem-backed and bare-metal GOT explicit
- Plan a hosted SimpleOS executable launch
   - Expected: hosted.executable_source equals `filesystem`
   - Expected: hosted.cache_strategy equals `mmap`
- Plan the explicit SimpleOS bare-metal fallback
   - Expected: baremetal.executable_source equals `baremetal_got`
   - Expected: baremetal.cache_strategy equals `simpleos_vfs_prewarm`


<details>
<summary>Executable SPipe</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-100
# @req REQ-101
# @req REQ-102
# @req REQ-SSPEC-SYSTEM
step("keeps hosted executable launch filesystem-backed and bare-metal GOT explicit")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Plan a hosted SimpleOS executable launch")
val hosted = startup_plan_from_metadata(
    "/sys/apps/simple.smf", [],
    launch_metadata_for_simpleos_path("/sys/apps/simple.smf"),
    true, false
)
expect(hosted.executable_source).to_equal("filesystem")
expect(hosted.cache_strategy).to_equal("mmap")

step("Plan the explicit SimpleOS bare-metal fallback")
val baremetal = startup_plan_from_metadata(
    "/sys/apps/simple.smf", [],
    launch_metadata_for_simpleos_baremetal_path("/sys/apps/simple.smf"),
    false, true
)
expect(baremetal.executable_source).to_equal("baremetal_got")
expect(baremetal.cache_strategy).to_equal("simpleos_vfs_prewarm")
```

</details>

#### plan SMF launch through SimpleOS VFS prewarm

- plan SMF launch through SimpleOS VFS prewarm
   - Expected: plan.target_os equals `simpleos`
   - Expected: plan.entry_kind equals `smf`
   - Expected: plan.cache_strategy equals `simpleos_vfs_prewarm`
   - Expected: plan.include_mmap_cache is true


- Verify: should plan SMF launch through SimpleOS VFS prewarm
   - Expected: plan.target_os equals `simpleos`
   - Expected: plan.entry_kind equals `smf`
   - Expected: plan.cache_strategy equals `simpleos_vfs_prewarm`
   - Expected: plan.include_mmap_cache is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("plan SMF launch through SimpleOS VFS prewarm")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val metadata = launch_metadata_for_simpleos_path("/sys/apps/simple.smf")
val plan = startup_plan_from_metadata("/sys/apps/simple.smf", [], metadata, false, true)
expect(plan.target_os).to_equal("simpleos")
expect(plan.entry_kind).to_equal("smf")
expect(plan.cache_strategy).to_equal("simpleos_vfs_prewarm")
expect(plan.include_mmap_cache).to_equal(true)
```

</details>

#### plan native SimpleOS app launch without app arg parser

- plan native SimpleOS app launch without app arg parser
   - Expected: plan.target_os equals `simpleos`
   - Expected: plan.entry_kind equals `native`
   - Expected: plan.include_arg_parser is false


- Verify: should plan native SimpleOS app launch without app arg parser
   - Expected: plan.target_os equals `simpleos`
   - Expected: plan.entry_kind equals `native`
   - Expected: plan.include_arg_parser is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("plan native SimpleOS app launch without app arg parser")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val metadata = launch_metadata_for_simpleos_path("/sys/apps/native_tool")
val plan = startup_plan_from_metadata("/sys/apps/native_tool", [], metadata, false, true)
expect(plan.target_os).to_equal("simpleos")
expect(plan.entry_kind).to_equal("native")
expect(plan.include_arg_parser).to_equal(false)
```

</details>

### REQ-101: WM hover prefetch

#### should prefetch cached executable bytes on hover without launching

- prefetch cached executable bytes on hover without launching
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
# @req REQ-SSPEC-SYSTEM
step("prefetch cached executable bytes on hover without launching")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
launcher_init()
app_registry_load_hardcoded_fallback()
app_registry_cache_bytes("/sys/apps/simple", [1u8, 2u8, 3u8])

val hit = launcher_hover_executable_icon("/sys/apps/simple.smf")

expect(hit).to_equal(true)
expect(launcher_prefetch_count()).to_equal(1)  # oracle: launcher_prefetch_count() must equal 1 — authoritative contract constant
expect(launcher_prefetch_last_path()).to_equal("/sys/apps/simple.smf")
expect(launcher_prefetch_last_cache_hit()).to_equal(true)
expect(launcher_get_running_app_count()).to_equal(0)  # oracle: launcher_get_running_app_count() must equal 0 — authoritative contract constant
expect(app_registry_cached_bytes("/sys/apps/simple").len()).to_equal(3)  # oracle: app_registry_cached_bytes("/sys/apps/simple").len() must equal 3 — authoritative contract constant
```

</details>

#### should record a miss for an executable that is not warmed yet

- record a miss for an executable that is not warmed yet
   - Expected: hit is false
   - Expected: launcher_prefetch_count() equals `1`
   - Expected: launcher_prefetch_last_path() equals `/sys/apps/editor.smf`
   - Expected: launcher_prefetch_last_cache_hit() is false
   - Expected: launcher_get_running_app_count() equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("record a miss for an executable that is not warmed yet")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
_clear_vfs_rootfs_for_test()
launcher_init()
app_registry_load_hardcoded_fallback()

val hit = launcher_hover_executable_icon("/sys/apps/editor.smf")

expect(hit).to_equal(false)
expect(launcher_prefetch_count()).to_equal(1)  # oracle: launcher_prefetch_count() must equal 1 — authoritative contract constant
expect(launcher_prefetch_last_path()).to_equal("/sys/apps/editor.smf")
expect(launcher_prefetch_last_cache_hit()).to_equal(false)
expect(launcher_get_running_app_count()).to_equal(0)  # oracle: launcher_get_running_app_count() must equal 0 — authoritative contract constant
```

</details>

#### warm executable bytes through VFS when hover finds an app file

- warm executable bytes through VFS when hover finds an app file
   - Expected: _mount_hosted_rootfs_for_test(_dbfs_root()) is true
   - Expected: g_vfs_write_file_text("/sys/apps/editor.smf", "SMF!!") is true
   - Expected: hit is true
   - Expected: launcher_prefetch_count() equals `1`
   - Expected: launcher_prefetch_last_path() equals `/sys/apps/editor.smf`
   - Expected: launcher_prefetch_last_cache_hit() is true
   - Expected: launcher_get_running_app_count() equals `0`
   - Expected: app_registry_cached_bytes("/sys/apps/editor").len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("warm executable bytes through VFS when hover finds an app file")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
_clear_vfs_rootfs_for_test()
expect(_mount_hosted_rootfs_for_test(_dbfs_root())).to_equal(true)
expect(g_vfs_write_file_text("/sys/apps/editor.smf", "SMF!!")).to_equal(true)
launcher_init()
app_registry_load_hardcoded_fallback()

val hit = launcher_hover_executable_icon("/sys/apps/editor.smf")

expect(hit).to_equal(true)
expect(launcher_prefetch_count()).to_equal(1)  # oracle: launcher_prefetch_count() must equal 1 — authoritative contract constant
expect(launcher_prefetch_last_path()).to_equal("/sys/apps/editor.smf")
expect(launcher_prefetch_last_cache_hit()).to_equal(true)
expect(launcher_get_running_app_count()).to_equal(0)  # oracle: launcher_get_running_app_count() must equal 0 — authoritative contract constant
expect(app_registry_cached_bytes("/sys/apps/editor").len()).to_equal(5)  # oracle: app_registry_cached_bytes("/sys/apps/editor").len() must equal 5 — authoritative contract constant
```

</details>

#### should reject empty hover paths without recording a prefetch

- reject empty hover paths without recording a prefetch
   - Expected: hit is false
   - Expected: launcher_prefetch_count() equals `0`
   - Expected: launcher_prefetch_last_path() equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reject empty hover paths without recording a prefetch")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
launcher_init()
val hit = launcher_hover_executable_icon("")
expect(hit).to_equal(false)
expect(launcher_prefetch_count()).to_equal(0)  # oracle: launcher_prefetch_count() must equal 0 — authoritative contract constant
expect(launcher_prefetch_last_path()).to_equal("")
```

</details>

### REQ-102: launcher icon index prefetch

#### should prefetch the executable path for a seeded launcher icon

- prefetch the executable path for a seeded launcher icon
   - Expected: hit is true
   - Expected: launcher_prefetch_count() equals `1`
   - Expected: launcher_prefetch_last_path() equals `/sys/apps/simple.smf`
   - Expected: launcher_get_running_app_count() equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prefetch the executable path for a seeded launcher icon")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
launcher_init()
app_registry_load_hardcoded_fallback()
app_registry_cache_bytes("/sys/apps/simple", [9u8])

val hit = launcher_prefetch_app_index(11)

expect(hit).to_equal(true)
expect(launcher_prefetch_count()).to_equal(1)  # oracle: launcher_prefetch_count() must equal 1 — authoritative contract constant
expect(launcher_prefetch_last_path()).to_equal("/sys/apps/simple.smf")
expect(launcher_get_running_app_count()).to_equal(0)  # oracle: launcher_get_running_app_count() must equal 0 — authoritative contract constant
```

</details>

#### should reject out-of-range icon indexes

- reject out-of-range icon indexes
   - Expected: hit is false
   - Expected: launcher_prefetch_count() equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reject out-of-range icon indexes")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
launcher_init()
val hit = launcher_prefetch_app_index(999u64)
expect(hit).to_equal(false)
expect(launcher_prefetch_count()).to_equal(0)  # oracle: launcher_prefetch_count() must equal 0 — authoritative contract constant
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simple_app_startup_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS app startup prefetch, REQ-100: SimpleOS launch metadata, REQ-101: WM hover prefetch, REQ-102: launcher icon index prefetch.
- SimpleOS app startup prefetch
- REQ-100: SimpleOS launch metadata
- REQ-101: WM hover prefetch
- REQ-102: launcher icon index prefetch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-100`
- `REQ-101`
- `REQ-102`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `224860c357b9578aec5da1e7ce2c3a730180c3815fa2754d29c353ef7ea16f74`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `224860c357b9578aec5da1e7ce2c3a730180c3815fa2754d29c353ef7ea16f74`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `224860c357b9578aec5da1e7ce2c3a730180c3815fa2754d29c353ef7ea16f74`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/03_system/app/simpleos/feature/simple_app_startup_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simple_app_startup_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos/feature/simple_app_startup_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simple_app_startup_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
