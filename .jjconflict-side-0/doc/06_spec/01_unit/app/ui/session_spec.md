# Session Specification

> 1. text widget

<!-- sdn-diagram:id=session_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=session_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

session_spec -> std
session_spec -> common
session_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=session_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Session Specification

## Scenarios

### UISession creation

#### creates session with initial state

1. text widget
2. expect session current mode
3. expect session current tree


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect session has surface
2. expect session surface count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("sess_main_root", "Main")
val tree = UITree.new(root)
val session = new_session(tree)
expect session.has_surface("main") to_equal true
expect session.surface_count() to_equal 1
```

</details>

#### creates session with pre-populated store

1. expect session current tree


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("sess_store_root", "Store")
val tree = UITree.new(root)
val store = WidgetStore.new()
val session = UISession.new_with_store(tree, store)
expect session.current_tree().root_id to_equal "sess_store_root"
```

</details>

### UISession dispatch

#### transitions to command mode

1. var session = new session
2. session dispatch
3. expect session current mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("sess_disp_root", "Cmd")
val tree = UITree.new(root)
var session = new_session(tree)
session.dispatch(UIEvent.CommandMode)
expect session.current_mode() to_equal "COMMAND"
```

</details>

#### transitions back to normal mode

1. var session = new session
2. session dispatch
3. session dispatch
4. expect session current mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. text widget
2. var session = new session
3. text widget
4. text widget
5. session update tree
6. expect session current tree
7. expect changes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var session = new session
2. session update tree


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect session viewport width
2. expect session viewport height
3. expect session active backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("sess_vp_root", "VP")
val tree = UITree.new(root)
val session = new_session(tree)
expect session.viewport_width() to_equal 80
expect session.viewport_height() to_equal 24
expect session.active_backend() to_equal "none"
```

</details>

#### sets viewport from active backend

1. var session = new session
2. session set viewport
3. expect session viewport width
4. expect session viewport height
5. expect session active backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var session = new session
2. session set viewport
3. session set viewport
4. expect session viewport width
5. expect session viewport height


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var session = new session
2. session set active backend
3. expect session active backend
4. session set viewport
5. expect session viewport width


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var session = new session
2. expect session surface count
3. expect session has surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var session = new session
2. expect session has surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var session = new session
2. session close surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var session = new session
2. expect session validate surface handle
3. session close surface
4. expect session validate surface handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect session active surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("sess_as_root", "Main")
val tree = UITree.new(root)
val session = new_session(tree)
expect session.active_surface() to_equal "main"
```

</details>

#### switches active surface

1. var session = new session
2. session open surface
3. session set active surface
4. expect session active surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("sess_as_sw_root", "Main")
val tree = UITree.new(root)
var session = new_session(tree)
val side_root = text_widget("sess_as_side_r", "Side")
val side_tree = UITree.new(side_root)
session.open_surface("sidebar", side_tree)
session.set_active_surface("sidebar")
expect session.active_surface() to_equal "sidebar"
```

</details>

### UISession update_surface_tree

#### updates surface tree via valid handle

1. var session = new session
2. session update surface tree


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var session = new session
2. session close surface
3. session update surface tree
4. expect session has surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect changes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = text_widget("sess_rc_root", "RC")
val tree = UITree.new(root)
val session = new_session(tree)
val changes = session.recent_changes(5)
expect changes.len() to_equal 0
```

</details>

#### returns formatted changelog after tree update

1. text widget
2. var session = new session
3. text widget
4. text widget
5. session update tree
6. expect changes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/ui/session_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
