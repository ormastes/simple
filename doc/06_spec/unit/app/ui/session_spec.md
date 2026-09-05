# Session Specification

> Tests covering UISession creation, UISession dispatch, UISession update_tree, UISession viewport, UISession surface lifecycle, UISession active surface, UISession update_surface_tree, UISession recent_changes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Session Specification

## Scenarios

### UISession creation

#### creates session with initial state

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates session with initial state


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates session with initial state")
val root = column("sess_root1", [
    text_widget("sess_t1", "Hello")
])
val tree = UITree.new(root)
val session = new_session(tree)
expect session.current_mode() to_equal "NORMAL"
expect session.current_tree().root_id to_equal "sess_root1"
```

</details>

#### creates session with main surface

- creates session with main surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates session with main surface")
val root = text_widget("sess_main_root", "Main")
val tree = UITree.new(root)
val session = new_session(tree)
expect session.has_surface("main") to_equal true
expect session.surface_count() to_equal 1
```

</details>

#### creates session with pre-populated store

- creates session with pre-populated store


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates session with pre-populated store")
val root = text_widget("sess_store_root", "Store")
val tree = UITree.new(root)
val store = WidgetStore.new()
val session = UISession.new_with_store(tree, store)
expect session.current_tree().root_id to_equal "sess_store_root"
```

</details>

#### resolves each tree theme without inheriting another session's WM material

- resolves each tree theme without inheriting another session's WM material


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves each tree theme without inheriting another session's WM material")
val snapshot = aetheric_dark_theme_render_snapshot()
apply_theme_render_snapshot_to_wm_chrome(snapshot)

var default_session = UISession.new(UITree.new(checkbox("session_alias", "Alias", false)))
val default_frame = default_session.submit_widget_draw_ir(96, 32, "cpu")
expect default_frame.batches[0].commands[1].color to_equal snapshot.material.solid_fallback_rgba

var distinct_session = UISession.new(UITree.new(checkbox("session_distinct", "Distinct", false)).with_theme("ios_light"))
val distinct_frame = distinct_session.submit_widget_draw_ir(96, 32, "cpu")
val distinct_snapshot = theme_package_render_snapshot("ios_light")
expect distinct_frame.batches[0].commands[1].color to_equal distinct_snapshot.material.solid_fallback_rgba
expect distinct_frame.batches[0].commands[1].color == snapshot.material.window_fill_rgba to_equal false
reset_wm_chrome_theme()
```

</details>

#### avoids optional active-snapshot aggregate binding in the session native path

- avoids optional active-snapshot aggregate binding in the session native path


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("avoids optional active-snapshot aggregate binding in the session native path")
val source = file_read("src/lib/nogc_sync_mut/ui/session.spl")
expect source to_contain "active_wm_theme_id()"
expect source to_contain "active_theme_id != \"\" and active_theme_id == resolved_theme"
expect source to_contain "active_wm_theme_snapshot_unchecked()"
expect source.contains("active_wm_theme_render_snapshot()") to_equal false
```

</details>

### UISession dispatch

#### transitions to command mode

- transitions to command mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transitions to command mode")
val root = text_widget("sess_disp_root", "Cmd")
val tree = UITree.new(root)
var session = new_session(tree)
session.dispatch(UIEvent.CommandMode)
expect session.current_mode() to_equal "COMMAND"
```

</details>

#### transitions back to normal mode

- transitions back to normal mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transitions back to normal mode")
val root = text_widget("sess_norm_root", "Norm")
val tree = UITree.new(root)
var session = new_session(tree)
session.dispatch(UIEvent.CommandMode)
session.dispatch(UIEvent.NormalMode)
expect session.current_mode() to_equal "NORMAL"
```

</details>

### UISession update_tree

#### updates tree and populates changelog

- updates tree and populates changelog


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("updates tree and populates changelog")
val root1 = column("sess_upd_root", [
    text_widget("sess_upd_t1", "Old")
])
val tree1 = UITree.new(root1)
var session = new_session(tree1)
# Build a new tree with an additional widget (InsertChild => Mount)
val root2 = column("sess_upd_root", [
    text_widget("sess_upd_t1", "Old"),
    text_widget("sess_upd_t2", "New")
])
val tree2 = UITree.new(root2)
session.update_tree(tree2)
expect session.current_tree().root_id to_equal "sess_upd_root"
# Changelog should have at least one entry (mount of new widget)
val changes = session.recent_changes(10)
expect changes.len() to_be_greater_than 0
```

</details>

#### updates main surface when tree changes

- updates main surface when tree changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("updates main surface when tree changes")
val root = text_widget("sess_surf_upd_r", "V1")
val tree1 = UITree.new(root)
var session = new_session(tree1)
val root2 = text_widget("sess_surf_upd_r", "V2")
val tree2 = UITree.new(root2)
session.update_tree(tree2)
val main_tree = session.get_surface("main")
expect main_tree != nil to_equal true
```

</details>

### UISession viewport

#### has default viewport

- has default viewport


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has default viewport")
val root = text_widget("sess_vp_root", "VP")
val tree = UITree.new(root)
val session = new_session(tree)
expect session.viewport_width() to_equal 80
expect session.viewport_height() to_equal 24
expect session.active_backend() to_equal "none"
```

</details>

#### sets viewport from active backend

- sets viewport from active backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets viewport from active backend")
val root = text_widget("sess_vp_set_root", "VP")
val tree = UITree.new(root)
var session = new_session(tree)
# With no active backend ("none"), any backend can set viewport
session.set_viewport(120, 40, "tui")
expect session.viewport_width() to_equal 120
expect session.viewport_height() to_equal 40
expect session.active_backend() to_equal "tui"
```

</details>

#### enforces active backend on viewport update

- enforces active backend on viewport update


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enforces active backend on viewport update")
val root = text_widget("sess_vp_enf_root", "VP")
val tree = UITree.new(root)
var session = new_session(tree)
session.set_viewport(120, 40, "tui")
# Different backend cannot update
session.set_viewport(1920, 1080, "tauri")
expect session.viewport_width() to_equal 120
expect session.viewport_height() to_equal 40
```

</details>

#### changes active backend

- changes active backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("changes active backend")
val root = text_widget("sess_vp_chg_root", "VP")
val tree = UITree.new(root)
var session = new_session(tree)
session.set_active_backend("tauri")
expect session.active_backend() to_equal "tauri"
# Now tauri can update viewport
session.set_viewport(1920, 1080, "tauri")
expect session.viewport_width() to_equal 1920
```

</details>

### UISession surface lifecycle

#### opens a new surface

- opens a new surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("opens a new surface")
val root = text_widget("sess_sl_root", "Main")
val tree = UITree.new(root)
var session = new_session(tree)
val popup_root = text_widget("sess_sl_popup_r", "Popup")
val popup_tree = UITree.new(popup_root)
val handle = session.open_surface("popup", popup_tree)
expect handle.id to_equal "popup"
expect session.surface_count() to_equal 2
expect session.has_surface("popup") to_equal true
```

</details>

#### closes a surface

- closes a surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("closes a surface")
val root = text_widget("sess_sl_close_r", "Main")
val tree = UITree.new(root)
var session = new_session(tree)
val dialog_root = text_widget("sess_sl_dialog_r", "Dialog")
val dialog_tree = UITree.new(dialog_root)
val handle = session.open_surface("dialog", dialog_tree)
val result = session.close_surface(handle)
expect result to_equal true
expect session.has_surface("dialog") to_equal false
```

</details>

#### prevents close with stale handle

- prevents close with stale handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prevents close with stale handle")
val root = text_widget("sess_sl_stale_r", "Main")
val tree = UITree.new(root)
var session = new_session(tree)
val tmp_root = text_widget("sess_sl_tmp_r", "Temp")
val tmp_tree = UITree.new(tmp_root)
val handle = session.open_surface("temp", tmp_tree)
session.close_surface(handle)
# Second close with same handle should fail
val result = session.close_surface(handle)
expect result to_equal false
```

</details>

#### validates surface handle

- validates surface handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates surface handle")
val root = text_widget("sess_sl_val_r", "Main")
val tree = UITree.new(root)
var session = new_session(tree)
val win_root = text_widget("sess_sl_win_r", "Win")
val win_tree = UITree.new(win_root)
val handle = session.open_surface("win", win_tree)
expect session.validate_surface_handle(handle) to_equal true
session.close_surface(handle)
expect session.validate_surface_handle(handle) to_equal false
```

</details>

### UISession active surface

#### defaults active to main

- defaults active to main


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults active to main")
val root = text_widget("sess_as_root", "Main")
val tree = UITree.new(root)
val session = new_session(tree)
expect session.active_surface() to_equal "main"
```

</details>

#### switches active surface

- switches active surface
   - Expected: session.close_surface(replacement_handle) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("switches active surface")
val root = text_widget("sess_as_sw_root", "Main")
val tree = UITree.new(root)
var session = new_session(tree)
val side_root = text_widget("sess_as_side_r", "Side")
val side_tree = UITree.new(side_root)
session.open_surface("sidebar", side_tree)
session.set_active_surface("sidebar")
expect session.active_surface() to_equal "sidebar"
expect session.current_tree().root_id to_equal "sess_as_side_r"
expect session.focused_widget() to_equal "sess_as_side_r"
val main_updated = UITree.new(text_widget("sess_as_main_updated", "Main Updated"))
session.update_tree(main_updated)
expect session.current_tree().root_id to_equal "sess_as_side_r"
val replacement = UITree.new(text_widget("sess_as_side_new", "Side New"))
val replacement_handle = session.open_surface("sidebar", replacement)
expect session.current_tree().root_id to_equal "sess_as_side_new"
session.set_active_surface("main")
expect session.current_tree().root_id to_equal "sess_as_main_updated"
expect session.focused_widget() to_equal "sess_as_main_updated"
session.set_active_surface("sidebar")
expect(session.close_surface(replacement_handle)).to_equal(true)
expect session.active_surface() to_equal "main"
expect session.current_tree().root_id to_equal "sess_as_main_updated"
```

</details>

### UISession update_surface_tree

#### updates surface tree via valid handle

- updates surface tree via valid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("updates surface tree via valid handle")
val root = text_widget("sess_ust_root", "Main")
val tree = UITree.new(root)
var session = new_session(tree)
val panel_root = text_widget("sess_ust_panel_r", "V1")
val panel_tree = UITree.new(panel_root)
val handle = session.open_surface("panel", panel_tree)
val panel_root2 = text_widget("sess_ust_panel_r", "V2")
val panel_tree2 = UITree.new(panel_root2)
session.update_surface_tree(handle, panel_tree2)
val updated = session.get_surface("panel")
expect updated != nil to_equal true
```

</details>

#### ignores update with stale handle

- ignores update with stale handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores update with stale handle")
val root = text_widget("sess_ust_stale_r", "Main")
val tree = UITree.new(root)
var session = new_session(tree)
val tmp_root = text_widget("sess_ust_tmp_r", "Temp")
val tmp_tree = UITree.new(tmp_root)
val handle = session.open_surface("tmp", tmp_tree)
session.close_surface(handle)
# Stale handle — update should be no-op
val new_root = text_widget("sess_ust_tmp_r", "V2")
val new_tree = UITree.new(new_root)
session.update_surface_tree(handle, new_tree)
expect session.has_surface("tmp") to_equal false
```

</details>

### UISession recent_changes

#### returns empty list initially

- returns empty list initially


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty list initially")
val root = text_widget("sess_rc_root", "RC")
val tree = UITree.new(root)
val session = new_session(tree)
val changes = session.recent_changes(5)
expect changes.len() to_equal 0
```

</details>

#### returns formatted changelog after tree update

- returns formatted changelog after tree update


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns formatted changelog after tree update")
val root1 = column("sess_rc_upd_root", [
    text_widget("sess_rc_t1", "Old")
])
val tree1 = UITree.new(root1)
var session = new_session(tree1)
val root2 = column("sess_rc_upd_root", [
    text_widget("sess_rc_t1", "Old"),
    text_widget("sess_rc_t2", "New")
])
val tree2 = UITree.new(root2)
session.update_tree(tree2)
val changes = session.recent_changes(10)
expect changes.len() to_be_greater_than 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/session_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering UISession creation, UISession dispatch, UISession update_tree, UISession viewport, UISession surface lifecycle, UISession active surface, UISession update_surface_tree, UISession recent_changes.
- UISession creation
- UISession dispatch
- UISession update_tree
- UISession viewport
- UISession surface lifecycle
- UISession active surface
- UISession update_surface_tree
- UISession recent_changes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
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

- Canonical SPipe generation for source `13bceaa22c723001c831166d7ddb2f89abd7e757b986f6ed46754fe814842aab`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `13bceaa22c723001c831166d7ddb2f89abd7e757b986f6ed46754fe814842aab`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `13bceaa22c723001c831166d7ddb2f89abd7e757b986f6ed46754fe814842aab`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/session_spec.spl
mirror: doc/06_spec/unit/app/ui/session_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/session_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/session_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/session_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates session with initial state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/session_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates session with main surface' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/session_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates session with pre-populated store' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
