# Window Scene Content Hit Migration Specification

> Tests covering SharedWmScene content hit-forest migration equivalence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Window Scene Content Hit Migration Specification

## Scenarios

### SharedWmScene content hit-forest migration equivalence

#### focuses the window when the body is clicked below the titlebar

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- focuses the window when the body is clicked below the titlebar
   - Expected: hit.action equals `focus_window`
   - Expected: hit.window_id equals `win1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("focuses the window when the body is clicked below the titlebar")
val scene = _one_window_scene()
val hit = shared_wm_dispatch_pointer(scene, _empty_taskbar(), 200, 150, "left", "down", 1000, "09:41", 0)
expect(hit.action).to_equal("focus_window")
expect(hit.window_id).to_equal("win1")
```

</details>

#### begins a drag when the titlebar is clicked away from any button

- begins a drag when the titlebar is clicked away from any button
   - Expected: hit.action equals `begin_drag_window`
   - Expected: hit.window_id equals `win1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("begins a drag when the titlebar is clicked away from any button")
val scene = _one_window_scene()
val hit = shared_wm_dispatch_pointer(scene, _empty_taskbar(), 200, 45, "left", "down", 1000, "09:41", 0)
expect(hit.action).to_equal("begin_drag_window")
expect(hit.window_id).to_equal("win1")
```

</details>

#### still begins a drag on the unwired green traffic-light button

- still begins a drag on the unwired green traffic-light button
   - Expected: hit.action equals `begin_drag_window`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("still begins a drag on the unwired green traffic-light button")
val scene = _one_window_scene()
# Absolute: local (48, 9) + window origin (10, 40) = (58, 49).
val hit = shared_wm_dispatch_pointer(scene, _empty_taskbar(), 58, 49, "left", "down", 1000, "09:41", 0)
expect(hit.action).to_equal("begin_drag_window")
```

</details>

#### closes the window when the close (X) button is clicked

- closes the window when the close (X) button is clicked
   - Expected: hit.action equals `close_window`
   - Expected: hit.window_id equals `win1`
   - Expected: hit.scene.windows.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("closes the window when the close (X) button is clicked")
val scene = _one_window_scene()
# Absolute: local (276, 2) + window origin (10, 40) = (286, 42).
val hit = shared_wm_dispatch_pointer(scene, _empty_taskbar(), 286, 42, "left", "down", 1000, "09:41", 0)
expect(hit.action).to_equal("close_window")
expect(hit.window_id).to_equal("win1")
expect(hit.scene.windows.len()).to_equal(0)
```

</details>

#### closes the window when the red traffic-light button is clicked

- closes the window when the red traffic-light button is clicked
   - Expected: hit.action equals `close_window`
   - Expected: hit.window_id equals `win1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("closes the window when the red traffic-light button is clicked")
val scene = _one_window_scene()
# Absolute: local (12, 9) + window origin (10, 40) = (22, 49).
val hit = shared_wm_dispatch_pointer(scene, _empty_taskbar(), 22, 49, "left", "down", 1000, "09:41", 0)
expect(hit.action).to_equal("close_window")
expect(hit.window_id).to_equal("win1")
```

</details>

#### minimizes the window when the yellow traffic-light button is clicked

- minimizes the window when the yellow traffic-light button is clicked
   - Expected: hit.action equals `minimize_window`
   - Expected: hit.window_id equals `win1`
   - Expected: hit.scene.windows[0].minimized is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("minimizes the window when the yellow traffic-light button is clicked")
val scene = _one_window_scene()
# Absolute: local (30, 9) + window origin (10, 40) = (40, 49).
val hit = shared_wm_dispatch_pointer(scene, _empty_taskbar(), 40, 49, "left", "down", 1000, "09:41", 0)
expect(hit.action).to_equal("minimize_window")
expect(hit.window_id).to_equal("win1")
expect(hit.scene.windows[0].minimized).to_equal(true)
```

</details>

#### falls through to desktop_background outside every window and chrome rect

- falls through to desktop_background outside every window and chrome rect
   - Expected: hit.action equals `desktop_background`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("falls through to desktop_background outside every window and chrome rect")
val scene = _one_window_scene()
val hit = shared_wm_dispatch_pointer(scene, _empty_taskbar(), 780, 300, "left", "down", 1000, "09:41", 0)
expect(hit.action).to_equal("desktop_background")
```

</details>

#### picks the topmost window by z-order when two windows overlap

- picks the topmost window by z-order when two windows overlap
   - Expected: hit.action equals `focus_window`
   - Expected: hit.window_id equals `surf2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("picks the topmost window by z-order when two windows overlap")
var manager = WindowManager.new()
val _one = manager.open_window("surf1", "One", 10, 40, 300, 200, _tree("one"))
val _two = manager.open_window("surf2", "Two", 80, 120, 300, 200, _tree("two"))
val registry = UiWindowSurfaceRegistry.new()
val scene = shared_wm_scene_from_window_manager(manager, registry, 800, 600)
# (150, 180) lies inside both window rects; "Two" opened later so it
# has the higher z_index and must win.
val hit = shared_wm_dispatch_pointer(scene, _empty_taskbar(), 150, 180, "left", "down", 1000, "09:41", 0)
expect(hit.action).to_equal("focus_window")
expect(hit.window_id).to_equal("surf2")
```

</details>

#### falls back to the lower window once the topmost is minimized

- falls back to the lower window once the topmost is minimized
   - Expected: hit.action equals `focus_window`
   - Expected: hit.window_id equals `surf1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("falls back to the lower window once the topmost is minimized")
var manager = WindowManager.new()
val _one = manager.open_window("surf1", "One", 10, 40, 300, 200, _tree("one"))
val _two = manager.open_window("surf2", "Two", 80, 120, 300, 200, _tree("two"))
manager.minimize_window("surf2")
val registry = UiWindowSurfaceRegistry.new()
val scene = shared_wm_scene_from_window_manager(manager, registry, 800, 600)
val hit = shared_wm_dispatch_pointer(scene, _empty_taskbar(), 150, 180, "left", "down", 1000, "09:41", 0)
expect(hit.action).to_equal("focus_window")
expect(hit.window_id).to_equal("surf1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/window_scene_content_hit_migration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SharedWmScene content hit-forest migration equivalence.
- SharedWmScene content hit-forest migration equivalence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8625cd449ef396426583c68839a0c294f545312eef35c8007402ce9186140f00`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8625cd449ef396426583c68839a0c294f545312eef35c8007402ce9186140f00`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8625cd449ef396426583c68839a0c294f545312eef35c8007402ce9186140f00`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/common/ui/window_scene_content_hit_migration_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/window_scene_content_hit_migration_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/window_scene_content_hit_migration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/window_scene_content_hit_migration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/window_scene_content_hit_migration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/window_scene_content_hit_migration_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'focuses the window when the body is clicked below the titlebar' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/window_scene_content_hit_migration_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'begins a drag when the titlebar is clicked away from any button' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/window_scene_content_hit_migration_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still begins a drag on the unwired green traffic-light button' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
