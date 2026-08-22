# simple_app_startup_spec

> Verifies the simple app startup behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_app_startup_spec

Verifies the simple app startup behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simple_app_startup_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the simple app startup behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### SimpleOS app startup prefetch

### REQ-100: SimpleOS launch metadata

#### keeps hosted executable launch filesystem-backed and bare-metal GOT explicit

- Verify: keeps hosted executable launch filesystem-backed and bare-metal GOT explicit
- Plan a hosted SimpleOS executable launch
   - Expected: hosted.executable_source equals `filesystem`
   - Expected: hosted.cache_strategy equals `mmap`
- Plan the explicit SimpleOS bare-metal fallback
   - Expected: baremetal.executable_source equals `baremetal_got`
   - Expected: baremetal.cache_strategy equals `simpleos_vfs_prewarm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-100 REQ-101 REQ-102
step("Verify: keeps hosted executable launch filesystem-backed and bare-metal GOT explicit")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

#### should plan SMF launch through SimpleOS VFS prewarm

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
# @req: REQ-100 REQ-101 REQ-102
step("Verify: should plan SMF launch through SimpleOS VFS prewarm")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val metadata = launch_metadata_for_simpleos_path("/sys/apps/simple.smf")
val plan = startup_plan_from_metadata("/sys/apps/simple.smf", [], metadata, false, true)
expect(plan.target_os).to_equal("simpleos")
expect(plan.entry_kind).to_equal("smf")
expect(plan.cache_strategy).to_equal("simpleos_vfs_prewarm")
expect(plan.include_mmap_cache).to_equal(true)
```

</details>

#### should plan native SimpleOS app launch without app arg parser

- Verify: should plan native SimpleOS app launch without app arg parser
   - Expected: plan.target_os equals `simpleos`
   - Expected: plan.entry_kind equals `native`
   - Expected: plan.include_arg_parser is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-100 REQ-101 REQ-102
step("Verify: should plan native SimpleOS app launch without app arg parser")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val metadata = launch_metadata_for_simpleos_path("/sys/apps/native_tool")
val plan = startup_plan_from_metadata("/sys/apps/native_tool", [], metadata, false, true)
expect(plan.target_os).to_equal("simpleos")
expect(plan.entry_kind).to_equal("native")
expect(plan.include_arg_parser).to_equal(false)
```

</details>

### REQ-101: WM hover prefetch

#### should prefetch cached executable bytes on hover without launching

- Verify: should prefetch cached executable bytes on hover without launching
   - Expected: hit is true
   - Expected: launcher_prefetch_count() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: launcher_prefetch_last_path() equals `/sys/apps/simple.smf`
   - Expected: launcher_prefetch_last_cache_hit() is true
   - Expected: launcher_get_running_app_count() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: app_registry_cached_bytes("/sys/apps/simple").len() equals `3)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-100 REQ-101 REQ-102
step("Verify: should prefetch cached executable bytes on hover without launching")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
launcher_init()
app_registry_load_hardcoded_fallback()
app_registry_cache_bytes("/sys/apps/simple", [1u8, 2u8, 3u8])

val hit = launcher_hover_executable_icon("/sys/apps/simple.smf")

expect(hit).to_equal(true)
expect(launcher_prefetch_count()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(launcher_prefetch_last_path()).to_equal("/sys/apps/simple.smf")
expect(launcher_prefetch_last_cache_hit()).to_equal(true)
expect(launcher_get_running_app_count()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(app_registry_cached_bytes("/sys/apps/simple").len()).to_equal(3)  # oracle: pinned constant asserted by this scenario
```

</details>

#### should record a miss for an executable that is not warmed yet

- Verify: should record a miss for an executable that is not warmed yet
   - Expected: hit is false
   - Expected: launcher_prefetch_count() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: launcher_prefetch_last_path() equals `/sys/apps/editor.smf`
   - Expected: launcher_prefetch_last_cache_hit() is false
   - Expected: launcher_get_running_app_count() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-100 REQ-101 REQ-102
step("Verify: should record a miss for an executable that is not warmed yet")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_clear_vfs_rootfs_for_test()
launcher_init()
app_registry_load_hardcoded_fallback()

val hit = launcher_hover_executable_icon("/sys/apps/editor.smf")

expect(hit).to_equal(false)
expect(launcher_prefetch_count()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(launcher_prefetch_last_path()).to_equal("/sys/apps/editor.smf")
expect(launcher_prefetch_last_cache_hit()).to_equal(false)
expect(launcher_get_running_app_count()).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### should warm executable bytes through VFS when hover finds an app file

- Verify: should warm executable bytes through VFS when hover finds an app file
   - Expected: _mount_hosted_rootfs_for_test(_dbfs_root()) is true
   - Expected: g_vfs_write_file_text("/sys/apps/editor.smf", "SMF!!") is true
   - Expected: hit is true
   - Expected: launcher_prefetch_count() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: launcher_prefetch_last_path() equals `/sys/apps/editor.smf`
   - Expected: launcher_prefetch_last_cache_hit() is true
   - Expected: launcher_get_running_app_count() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: app_registry_cached_bytes("/sys/apps/editor").len() equals `5)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-100 REQ-101 REQ-102
step("Verify: should warm executable bytes through VFS when hover finds an app file")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
_clear_vfs_rootfs_for_test()
expect(_mount_hosted_rootfs_for_test(_dbfs_root())).to_equal(true)
expect(g_vfs_write_file_text("/sys/apps/editor.smf", "SMF!!")).to_equal(true)
launcher_init()
app_registry_load_hardcoded_fallback()

val hit = launcher_hover_executable_icon("/sys/apps/editor.smf")

expect(hit).to_equal(true)
expect(launcher_prefetch_count()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(launcher_prefetch_last_path()).to_equal("/sys/apps/editor.smf")
expect(launcher_prefetch_last_cache_hit()).to_equal(true)
expect(launcher_get_running_app_count()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(app_registry_cached_bytes("/sys/apps/editor").len()).to_equal(5)  # oracle: pinned constant asserted by this scenario
```

</details>

#### should reject empty hover paths without recording a prefetch

- Verify: should reject empty hover paths without recording a prefetch
   - Expected: hit is false
   - Expected: launcher_prefetch_count() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: launcher_prefetch_last_path() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-100 REQ-101 REQ-102
step("Verify: should reject empty hover paths without recording a prefetch")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
launcher_init()
val hit = launcher_hover_executable_icon("")
expect(hit).to_equal(false)
expect(launcher_prefetch_count()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(launcher_prefetch_last_path()).to_equal("")
```

</details>

### REQ-102: launcher icon index prefetch

#### should prefetch the executable path for a seeded launcher icon

- Verify: should prefetch the executable path for a seeded launcher icon
   - Expected: hit is true
   - Expected: launcher_prefetch_count() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: launcher_prefetch_last_path() equals `/sys/apps/simple.smf`
   - Expected: launcher_get_running_app_count() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-100 REQ-101 REQ-102
step("Verify: should prefetch the executable path for a seeded launcher icon")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
launcher_init()
app_registry_load_hardcoded_fallback()
app_registry_cache_bytes("/sys/apps/simple", [9u8])

val hit = launcher_prefetch_app_index(11)

expect(hit).to_equal(true)
expect(launcher_prefetch_count()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(launcher_prefetch_last_path()).to_equal("/sys/apps/simple.smf")
expect(launcher_get_running_app_count()).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### should reject out-of-range icon indexes

- Verify: should reject out-of-range icon indexes
   - Expected: hit is false
   - Expected: launcher_prefetch_count() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-100 REQ-101 REQ-102
step("Verify: should reject out-of-range icon indexes")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
launcher_init()
val hit = launcher_prefetch_app_index(999u64)
expect(hit).to_equal(false)
expect(launcher_prefetch_count()).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3660eb62bf05d4e2faf6e8c32411f6ab4353d9dbdd3385b8cc97f7bc35f3fae6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3660eb62bf05d4e2faf6e8c32411f6ab4353d9dbdd3385b8cc97f7bc35f3fae6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3660eb62bf05d4e2faf6e8c32411f6ab4353d9dbdd3385b8cc97f7bc35f3fae6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/simpleos/feature/simple_app_startup_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simple_app_startup_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos/feature/simple_app_startup_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/simpleos/feature/simple_app_startup_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simple_app_startup_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos/feature/simple_app_startup_spec.spl:73:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should plan SMF launch through SimpleOS VFS prewarm' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simple_app_startup_spec.spl:84:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should plan native SimpleOS app launch without app arg parser' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simple_app_startup_spec.spl:95:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should prefetch cached executable bytes on hover without launching' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simple_app_startup_spec.spl:112:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should record a miss for an executable that is not warmed yet' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simple_app_startup_spec.spl:128:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should warm executable bytes through VFS when hover finds an app file' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simple_app_startup_spec.spl:147:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject empty hover paths without recording a prefetch' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
