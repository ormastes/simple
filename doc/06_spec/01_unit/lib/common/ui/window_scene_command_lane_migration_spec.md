# window_scene_command_lane_migration_spec

> Pre-migration equivalence baseline for window-manager

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# window_scene_command_lane_migration_spec

Pre-migration equivalence baseline for window-manager

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/window_scene_command_lane_migration_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Pre-migration equivalence baseline for window-manager
    command-lane hit testing and dispatch behavior.

## Scenarios

### WM command-lane dispatch migration

#### command_lane_clock_center

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
val scene = _empty_scene()
val chrome = shared_wm_scene_chrome(scene, 1000, "12:34", 3, 0)
val result = _shared_wm_command_lane_dispatch(scene, chrome, 1780)
assert_true(result.action == "command_lane_clock" and result.target_id == "clock")
```

</details>

#### command_lane_icon

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
val scene = _empty_scene()
val chrome = shared_wm_scene_chrome(scene, 1000, "12:34", 3, 0)
val result = _shared_wm_command_lane_dispatch(scene, chrome, 1850)
assert_true(result.action == "command_lane_icon" and result.target_id.contains("right_icon"))
```

</details>

#### command_lane_default

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
val scene = _empty_scene()
val chrome = shared_wm_scene_chrome(scene, 1000, "12:34", 3, 0)
val result = _shared_wm_command_lane_dispatch(scene, chrome, 500)
assert_true(result.action == "command_lane" and result.target_id == "command_lane")
```

</details>

#### command_lane_zero_icons_clock

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
val scene = _empty_scene()
val chrome = shared_wm_scene_chrome(scene, 1000, "12:34", 0, 0)
val result = _shared_wm_command_lane_dispatch(scene, chrome, 1848)
assert_true(result.action == "command_lane_clock" and result.target_id == "clock")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d688ae5747a12955400b692d965c8a9bbffa5172763aa830b5ab3c8bd3578950`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d688ae5747a12955400b692d965c8a9bbffa5172763aa830b5ab3c8bd3578950`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d688ae5747a12955400b692d965c8a9bbffa5172763aa830b5ab3c8bd3578950`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/common/ui/window_scene_command_lane_migration_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/window_scene_command_lane_migration_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/window_scene_command_lane_migration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/window_scene_command_lane_migration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/window_scene_command_lane_migration_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/common/ui/window_scene_command_lane_migration_spec.spl:28:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'command_lane_clock_center' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/ui/window_scene_command_lane_migration_spec.spl:35:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'command_lane_icon' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/ui/window_scene_command_lane_migration_spec.spl:42:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'command_lane_default' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/ui/window_scene_command_lane_migration_spec.spl:49:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'command_lane_zero_icons_clock' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
