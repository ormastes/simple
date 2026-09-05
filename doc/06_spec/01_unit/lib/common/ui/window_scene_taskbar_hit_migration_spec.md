# Window Scene Taskbar Hit Migration Specification

> Tests covering SharedWmScene taskbar hit-forest migration equivalence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Window Scene Taskbar Hit Migration Specification

## Scenarios

### SharedWmScene taskbar hit-forest migration equivalence

#### hits pinned slot 0 across its whole 56px column, not past it

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- hits pinned slot 0 across its whole 56px column, not past it
   - Expected: at_left_edge.action equals `launch_app`
   - Expected: at_left_edge.app_id equals `terminal`
   - Expected: at_right_edge.action equals `launch_app`
   - Expected: at_right_edge.app_id equals `terminal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hits pinned slot 0 across its whole 56px column, not past it")
val scene = _hit_scene()
val taskbar = _hit_taskbar()
val at_left_edge = shared_wm_dispatch_pointer(scene, taskbar, 0, 575, "left", "down", 1000, "09:41", 2)
val at_right_edge = shared_wm_dispatch_pointer(scene, taskbar, 55, 575, "left", "down", 1000, "09:41", 2)
expect(at_left_edge.action).to_equal("launch_app")
expect(at_left_edge.app_id).to_equal("terminal")
expect(at_right_edge.action).to_equal("launch_app")
expect(at_right_edge.app_id).to_equal("terminal")
```

</details>

#### hits pinned slot 1 starting exactly at the 56px boundary

- hits pinned slot 1 starting exactly at the 56px boundary
   - Expected: at_boundary.action equals `launch_app`
   - Expected: at_boundary.app_id equals `browser`
   - Expected: at_right_edge.action equals `launch_app`
   - Expected: at_right_edge.app_id equals `browser`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hits pinned slot 1 starting exactly at the 56px boundary")
val scene = _hit_scene()
val taskbar = _hit_taskbar()
val at_boundary = shared_wm_dispatch_pointer(scene, taskbar, 56, 575, "left", "down", 1000, "09:41", 2)
val at_right_edge = shared_wm_dispatch_pointer(scene, taskbar, 111, 575, "left", "down", 1000, "09:41", 2)
expect(at_boundary.action).to_equal("launch_app")
expect(at_boundary.app_id).to_equal("browser")
expect(at_right_edge.action).to_equal("launch_app")
expect(at_right_edge.app_id).to_equal("browser")
```

</details>

#### hits the running-window slot 2 and focuses the existing window

- hits the running-window slot 2 and focuses the existing window
   - Expected: at_boundary.action equals `focus_window`
   - Expected: at_boundary.window_id equals `win1`
   - Expected: at_right_edge.action equals `focus_window`
   - Expected: at_right_edge.window_id equals `win1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hits the running-window slot 2 and focuses the existing window")
val scene = _hit_scene()
val taskbar = _hit_taskbar()
val at_boundary = shared_wm_dispatch_pointer(scene, taskbar, 112, 575, "left", "down", 1000, "09:41", 2)
val at_right_edge = shared_wm_dispatch_pointer(scene, taskbar, 167, 575, "left", "down", 1000, "09:41", 2)
expect(at_boundary.action).to_equal("focus_window")
expect(at_boundary.window_id).to_equal("win1")
expect(at_right_edge.action).to_equal("focus_window")
expect(at_right_edge.window_id).to_equal("win1")
```

</details>

#### falls through to taskbar_empty exactly past the last slot's right edge

- falls through to taskbar_empty exactly past the last slot's right edge
   - Expected: past_last_slot.action equals `taskbar_empty`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls through to taskbar_empty exactly past the last slot's right edge")
val scene = _hit_scene()
val taskbar = _hit_taskbar()
val past_last_slot = shared_wm_dispatch_pointer(scene, taskbar, 168, 575, "left", "down", 1000, "09:41", 2)
expect(past_last_slot.action).to_equal("taskbar_empty")
```

</details>

#### right-click on a pinned slot unpins it; right-click on a running slot pins it

- right-click on a pinned slot unpins it; right-click on a running slot pins it
   - Expected: unpin.action equals `unpin_app`
   - Expected: unpin.app_id equals `terminal`
   - Expected: pin.action equals `pin_app`
   - Expected: pin.app_id equals `demo.app`
   - Expected: pin.window_id equals `win1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("right-click on a pinned slot unpins it; right-click on a running slot pins it")
val scene = _hit_scene()
val taskbar = _hit_taskbar()
val unpin = shared_wm_dispatch_pointer(scene, taskbar, 0, 575, "right", "down", 1000, "09:41", 2)
val pin = shared_wm_dispatch_pointer(scene, taskbar, 112, 575, "right", "down", 1000, "09:41", 2)
expect(unpin.action).to_equal("unpin_app")
expect(unpin.app_id).to_equal("terminal")
expect(pin.action).to_equal("pin_app")
expect(pin.app_id).to_equal("demo.app")
expect(pin.window_id).to_equal("win1")
```

</details>

#### reports taskbar_empty when there are no pinned or running apps at all

- reports taskbar_empty when there are no pinned or running apps at all
   - Expected: clicked.action equals `taskbar_empty`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports taskbar_empty when there are no pinned or running apps at all")
val scene = _hit_scene()
val empty_taskbar = TaskbarModel(pinned: [], running: [], tray: [])
val clicked = shared_wm_dispatch_pointer(scene, empty_taskbar, 0, 575, "left", "down", 1000, "09:41", 2)
expect(clicked.action).to_equal("taskbar_empty")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/window_scene_taskbar_hit_migration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SharedWmScene taskbar hit-forest migration equivalence.
- SharedWmScene taskbar hit-forest migration equivalence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `d21a765796b63a221855d729f33810c21dd7954f948960a07c142ed673409f54`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d21a765796b63a221855d729f33810c21dd7954f948960a07c142ed673409f54`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d21a765796b63a221855d729f33810c21dd7954f948960a07c142ed673409f54`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/window_scene_taskbar_hit_migration_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/window_scene_taskbar_hit_migration_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/window_scene_taskbar_hit_migration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/window_scene_taskbar_hit_migration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/window_scene_taskbar_hit_migration_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hits pinned slot 0 across its whole 56px column, not past it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/window_scene_taskbar_hit_migration_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hits pinned slot 1 starting exactly at the 56px boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/window_scene_taskbar_hit_migration_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hits the running-window slot 2 and focuses the existing window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
