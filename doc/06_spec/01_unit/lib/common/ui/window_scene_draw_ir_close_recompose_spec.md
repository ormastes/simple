# Window Scene Draw Ir Close Recompose Specification

> Tests covering WM Draw IR window card layer projection, close lifecycle through the runtime dispatch adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Window Scene Draw Ir Close Recompose Specification

## Scenarios

### WM Draw IR window card layer projection

#### projects three window cards bottom-to-top by z-index

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- projects three window cards bottom-to-top by z-index
   - Expected: ids.len() equals `3`
   - Expected: ids[0] equals `win1`
   - Expected: ids[1] equals `win2`
   - Expected: ids[2] equals `win3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("projects three window cards bottom-to-top by z-index")
val ids = _layer_ids(_three_window_scene())
expect(ids.len()).to_equal(3)
expect(ids[0]).to_equal("win1")
expect(ids[1]).to_equal("win2")
expect(ids[2]).to_equal("win3")
```

</details>

#### projects two cards and no stale card after a close dispatch

- projects two cards and no stale card after a close dispatch
   - Expected: closed.action equals `close_window`
   - Expected: closed.window_id equals `win2`
   - Expected: ids.len() equals `2`
   - Expected: ids[0] equals `win1`
   - Expected: ids[1] equals `win3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("projects two cards and no stale card after a close dispatch")
val scene = _three_window_scene()
# win2 close X spans [426,446)x[152,172), uncovered by win1/win3.
val closed = shared_wm_dispatch_pointer(scene, _taskbar_empty(), 436, 162, "left", "down", 1000, "", 0)
expect(closed.action).to_equal("close_window")
expect(closed.window_id).to_equal("win2")
val ids = _layer_ids(closed.scene)
expect(ids.len()).to_equal(2)
expect(ids[0]).to_equal("win1")
expect(ids[1]).to_equal("win3")
```

</details>

#### drops a minimized card from the projection but keeps the scene entry

- drops a minimized card from the projection but keeps the scene entry
   - Expected: minimized.action equals `minimize_window`
   - Expected: ids.len() equals `2`
   - Expected: ids[0] equals `win1`
   - Expected: ids[1] equals `win2`
   - Expected: minimized.scene.windows.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("drops a minimized card from the projection but keeps the scene entry")
val scene = _three_window_scene()
# win3 yellow traffic light center (235,214).
val minimized = shared_wm_dispatch_pointer(scene, _taskbar_empty(), 235, 214, "left", "down", 1000, "", 0)
expect(minimized.action).to_equal("minimize_window")
val ids = _layer_ids(minimized.scene)
expect(ids.len()).to_equal(2)
expect(ids[0]).to_equal("win1")
expect(ids[1]).to_equal("win2")
expect(minimized.scene.windows.len()).to_equal(3)
```

</details>

#### keeps equal-z card order stable across an unrelated close

- keeps equal-z card order stable across an unrelated close
   - Expected: closed.action equals `close_window`
   - Expected: closed.window_id equals `win4`
   - Expected: ids.len() equals `3`
   - Expected: ids[0] equals `win1`
   - Expected: ids[1] equals `win2`
   - Expected: ids[2] equals `win3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps equal-z card order stable across an unrelated close")
val scene = simple_gui_internal_window_scene(800, 600, "cpu", [
    _win(1, 100, 100, 5, false),
    _win(2, 150, 150, 5, false),
    _win(3, 200, 200, 5, true),
    _win(4, 250, 250, 9, false)
])
# Close win4 (top, z 9) via its close X: [526,546)x[252,272).
val closed = shared_wm_dispatch_pointer(scene, _taskbar_empty(), 536, 262, "left", "down", 1000, "", 0)
expect(closed.action).to_equal("close_window")
expect(closed.window_id).to_equal("win4")
val ids = _layer_ids(closed.scene)
expect(ids.len()).to_equal(3)
expect(ids[0]).to_equal("win1")
expect(ids[1]).to_equal("win2")
expect(ids[2]).to_equal("win3")
```

</details>

#### changes the card revision identity across lifecycle state changes

- changes the card revision identity across lifecycle state changes
   - Expected: closed.action equals `close_window`
   - Expected: focus_rev_changed is true
   - Expected: min_rev_changed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("changes the card revision identity across lifecycle state changes")
val scene = _three_window_scene()
val before = _wm_draw_ir_window_revision(scene.windows[1])
# Closing focused win3 refocuses win2 -> win2's revision must change so
# a revision-keyed renderer repaints its titlebar as focused.
val closed = shared_wm_dispatch_pointer(scene, _taskbar_empty(), 486, 212, "left", "down", 1000, "", 0)
expect(closed.action).to_equal("close_window")
val after = _wm_draw_ir_window_revision(closed.scene.windows[1])
# Seed landmine: an inline `==` inside expect() mis-evaluates as an
# expect/to_equal pair, so compare via a precomputed bool.
val focus_rev_changed = before != after
expect(focus_rev_changed).to_equal(true)
# Minimizing changes the minimized facet of the SAME window's revision.
val min_scene = shared_wm_minimize_window_by_window_id(scene, "win1")
val min_rev = _wm_draw_ir_window_revision(min_scene.windows[0])
val orig_rev = _wm_draw_ir_window_revision(scene.windows[0])
val min_rev_changed = min_rev != orig_rev
expect(min_rev_changed).to_equal(true)
```

</details>

#### records the seed-blocked full-composition assertions as explicit skips

- records the seed-blocked full-composition assertions as explicit skips
   - Expected: closed.action equals `close_window`
   - Expected: shared_wm_focused_window_id(closed.scene) equals `win2`
   - Expected: ids.len() equals `2`
   - Expected: ids[1] equals `win2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("records the seed-blocked full-composition assertions as explicit skips")
# std.spec skip() prints are swallowed by the seed's cross-module
# evaluator defect, so record the skips with direct prints.
print "    SKIP composing 3 windows yields 3 card batches with close/traffic nodes: seed crashes in resolve_font_metrics_with_language — see doc/08_tracking/bug/font_renderer_resolve_metrics_nil_receiver_seed_2026-07-20.md"
print "    SKIP recompose after close leaves no stale win2 nodes and changes scene key: same font_renderer nil-receiver crash"
print "    SKIP dispatch honors exactly the drawn close/traffic rects (lockstep): same font_renderer nil-receiver crash"
# oracle: real, executable stand-in for the skipped lockstep half —
# closing focused win3 must refocus the next window win2 and leave it
# visible in the layer projection, which is the precondition the
# (seed-blocked) full-composition skips rely on.
val scene = _three_window_scene()
val closed = shared_wm_dispatch_pointer(scene, _taskbar_empty(), 486, 212, "left", "down", 1000, "", 0)
expect(closed.action).to_equal("close_window")
expect(shared_wm_focused_window_id(closed.scene)).to_equal("win2")
val ids = _layer_ids(closed.scene)
expect(ids.len()).to_equal(2)
expect(ids[1]).to_equal("win2")
```

</details>

### close lifecycle through the runtime dispatch adapter

#### a close dispatch maps to a handled window_close command with stable wire form

- a close dispatch maps to a handled window_close command with stable wire form
   - Expected: command.kind equals `window_close`
   - Expected: command.handled is true
   - Expected: command.window_id equals `win3`
   - Expected: command.target_id equals `surf3`
   - Expected: wm_runtime_dispatch_wire(command) equals `kind=window_close;target=surf3;app=app3;window=win3;handled=true;payload=surf... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a close dispatch maps to a handled window_close command with stable wire form")
val scene = _three_window_scene()
val closed = shared_wm_dispatch_pointer(scene, _taskbar_empty(), 486, 212, "left", "down", 1000, "", 0)
val command = wm_runtime_command_from_shared_dispatch(closed)
expect(command.kind).to_equal("window_close")
expect(command.handled).to_equal(true)
expect(command.window_id).to_equal("win3")
expect(command.target_id).to_equal("surf3")
expect(wm_runtime_dispatch_wire(command)).to_equal("kind=window_close;target=surf3;app=app3;window=win3;handled=true;payload=surface_id=surf3;window_id=win3")
```

</details>

#### a minimize dispatch maps to a handled window_minimize command

- a minimize dispatch maps to a handled window_minimize command
   - Expected: command.kind equals `window_minimize`
   - Expected: command.handled is true
   - Expected: command.window_id equals `win3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a minimize dispatch maps to a handled window_minimize command")
val scene = _three_window_scene()
val minimized = shared_wm_dispatch_pointer(scene, _taskbar_empty(), 235, 214, "left", "down", 1000, "", 0)
val command = wm_runtime_command_from_shared_dispatch(minimized)
expect(command.kind).to_equal("window_minimize")
expect(command.handled).to_equal(true)
expect(command.window_id).to_equal("win3")
```

</details>

#### applying a close clears focus and records the closed window id

- applying a close clears focus and records the closed window id
   - Expected: focus.action equals `focus_window`
   - Expected: state.focused_window_id equals `win3`
   - Expected: state.last_command_kind equals `window_close`
   - Expected: state.focused_window_id equals ``
   - Expected: state.closed_window_ids.len() equals `1`
   - Expected: state.closed_window_ids[0] equals `win3`
   - Expected: state.minimized_window_ids.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applying a close clears focus and records the closed window id")
val scene = _three_window_scene()
var state = wm_runtime_shell_state_empty()
# Focus win3 through a real body click first, then close it.
val focus = shared_wm_dispatch_pointer(scene, _taskbar_empty(), 350, 350, "left", "down", 1000, "", 0)
expect(focus.action).to_equal("focus_window")
state = wm_runtime_apply_shared_dispatch(state, focus)
expect(state.focused_window_id).to_equal("win3")
val closed = shared_wm_dispatch_pointer(scene, _taskbar_empty(), 486, 212, "left", "down", 1000, "", 0)
state = wm_runtime_apply_shared_dispatch(state, closed)
expect(state.last_command_kind).to_equal("window_close")
expect(state.focused_window_id).to_equal("")
expect(state.closed_window_ids.len()).to_equal(1)
expect(state.closed_window_ids[0]).to_equal("win3")
expect(state.minimized_window_ids.len()).to_equal(0)
```

</details>

#### applying a minimize records the minimized window id and drops its focus

- applying a minimize records the minimized window id and drops its focus
   - Expected: state.last_command_kind equals `window_minimize`
   - Expected: state.focused_window_id equals ``
   - Expected: state.minimized_window_ids.len() equals `1`
   - Expected: state.minimized_window_ids[0] equals `win3`
   - Expected: state.closed_window_ids.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applying a minimize records the minimized window id and drops its focus")
val scene = _three_window_scene()
var state = wm_runtime_shell_state_empty()
val focus = shared_wm_dispatch_pointer(scene, _taskbar_empty(), 350, 350, "left", "down", 1000, "", 0)
state = wm_runtime_apply_shared_dispatch(state, focus)
val minimized = shared_wm_dispatch_pointer(scene, _taskbar_empty(), 235, 214, "left", "down", 1000, "", 0)
state = wm_runtime_apply_shared_dispatch(state, minimized)
expect(state.last_command_kind).to_equal("window_minimize")
expect(state.focused_window_id).to_equal("")
expect(state.minimized_window_ids.len()).to_equal(1)
expect(state.minimized_window_ids[0]).to_equal("win3")
expect(state.closed_window_ids.len()).to_equal(0)
```

</details>

#### closing an unfocused window keeps the current focus owner

- closing an unfocused window keeps the current focus owner
   - Expected: closed.window_id equals `win1`
   - Expected: state.focused_window_id equals `win3`
   - Expected: state.closed_window_ids[0] equals `win1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("closing an unfocused window keeps the current focus owner")
val scene = _three_window_scene()
var state = wm_runtime_shell_state_empty()
val focus = shared_wm_dispatch_pointer(scene, _taskbar_empty(), 350, 350, "left", "down", 1000, "", 0)
state = wm_runtime_apply_shared_dispatch(state, focus)
# win1 close X at [376,396)x[102,122) is uncovered.
val closed = shared_wm_dispatch_pointer(scene, _taskbar_empty(), 386, 112, "left", "down", 1000, "", 0)
expect(closed.window_id).to_equal("win1")
state = wm_runtime_apply_shared_dispatch(state, closed)
expect(state.focused_window_id).to_equal("win3")
expect(state.closed_window_ids[0]).to_equal("win1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/window_scene_draw_ir_close_recompose_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WM Draw IR window card layer projection, close lifecycle through the runtime dispatch adapter.
- WM Draw IR window card layer projection
- close lifecycle through the runtime dispatch adapter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `53306821d469c5c601e0ee043d237374af7fa9338a86ce61ee9cef34f424b187`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `53306821d469c5c601e0ee043d237374af7fa9338a86ce61ee9cef34f424b187`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `53306821d469c5c601e0ee043d237374af7fa9338a86ce61ee9cef34f424b187`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/ui/window_scene_draw_ir_close_recompose_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/window_scene_draw_ir_close_recompose_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/window_scene_draw_ir_close_recompose_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/window_scene_draw_ir_close_recompose_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/window_scene_draw_ir_close_recompose_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/window_scene_draw_ir_close_recompose_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'projects three window cards bottom-to-top by z-index' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/window_scene_draw_ir_close_recompose_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'projects two cards and no stale card after a close dispatch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/window_scene_draw_ir_close_recompose_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'drops a minimized card from the projection but keeps the scene entry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
