# wm_action_applier_spec

> Verifies the wm action applier behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# wm_action_applier_spec

Verifies the wm action applier behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/wm_action_applier_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the wm action applier behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### shared WM action applier

#### creates windows through shared compositor logic

- Verify: creates windows through shared compositor logic
   - Expected: compositor.surfaces.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: compositor.surfaces[0].app_id equals `app.test`
   - Expected: compositor.surfaces[0].content_html equals `tree`
   - Expected: compositor.surfaces[0].content_revision equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-014 REQ-WEB-BROWSER-016
step("Verify: creates windows through shared compositor logic")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var compositor = Compositor.with_backends(ApplierBackend(w: 200, h: 120), nil, 200, 120)
val result = apply_wm_action_to_compositor(compositor, _action("create_window", 0))
compositor = result.compositor
val wid = result.window_id
assert_true(wid > 0)
expect(compositor.surfaces.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(compositor.surfaces[0].app_id).to_equal("app.test")
expect(compositor.surfaces[0].content_html).to_equal("tree")
expect(compositor.surfaces[0].content_revision).to_equal(2)  # oracle: pinned constant asserted by this scenario
```

</details>

#### materializes shared GUI WindowManager state into SimpleOS compositor surfaces

- Verify: materializes shared GUI WindowManager state into SimpleOS compositor surfaces
   - Expected: ids.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: compositor.surfaces.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: compositor.surfaces[0].title equals `Simple App`
   - Expected: compositor.surfaces[0].session.root_id equals `app_root`
   - Expected: compositor.surfaces[0].process_id equals `55)  # oracle: pinned constant asserted by this scenario`
   - Expected: compositor.surfaces[0].app_id equals `simple.app`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-014 REQ-WEB-BROWSER-016
step("Verify: materializes shared GUI WindowManager state into SimpleOS compositor surfaces")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var manager = WindowManager.new()
val _opened = manager.open_window("surf1", "Simple App", 12, 18, 160, 120, _shared_tree("app"))
var registry = UiWindowSurfaceRegistry.new()
registry.bind_with_kind("win1", "surf1", 55u64, "simple.app", "Simple App", UI_SURFACE_KIND_SIMPLE_WEB)
val scene = shared_wm_scene_from_window_manager(manager, registry, 320, 240)
var compositor = Compositor.with_backends(ApplierBackend(w: 320, h: 240), nil, 320, 240)

val ids = compositor.create_windows_from_shared_scene(scene)

expect(ids.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(compositor.surfaces.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(compositor.surfaces[0].title).to_equal("Simple App")
expect(compositor.surfaces[0].session.root_id).to_equal("app_root")
expect(compositor.surfaces[0].process_id).to_equal(55)  # oracle: pinned constant asserted by this scenario
expect(compositor.surfaces[0].app_id).to_equal("simple.app")
```

</details>

#### creates web windows with a Simple Web render request surface

- Verify: creates web windows with a Simple Web render request surface
   - Expected: compositor.surfaces.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: compositor.surfaces[0].title equals `Simple Browser`
   - Expected: compositor.surfaces[0].content_handle equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: compositor.surfaces[0].content_revision equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: req.target equals `simple_web`
   - Expected: req.surface_id equals `web_window_77`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-014 REQ-WEB-BROWSER-016
step("Verify: creates web windows with a Simple Web render request surface")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var compositor = Compositor.with_backends(ApplierBackend(w: 200, h: 120), nil, 200, 120)
val action = WmAction(kind: "create_web_window", window_id: 0, title: "Simple Browser", x: 4, y: 6, width: 96, height: 72, content: "https://example.test", process_id: 700, app_id: "/host/browser", owner_port: 42, src_port: 0)
val result = apply_wm_action_to_compositor(compositor, action)
compositor = result.compositor
assert_true(result.applied)
expect(compositor.surfaces.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(compositor.surfaces[0].title).to_equal("Simple Browser")
expect(compositor.surfaces[0].content_kind).to_equal(
    WM_CONTENT_KIND_WEB_DOCUMENT
)
expect(compositor.surfaces[0].content_handle).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(compositor.surfaces[0].content_html).to_contain("https://example.test")
expect(compositor.surfaces[0].content_revision).to_equal(2)  # oracle: pinned constant asserted by this scenario

val req = wm_action_web_window_request(77, "Browser", "about:blank", 64, 48)
expect(req.target).to_equal("simple_web")
expect(req.surface_id).to_equal("web_window_77")
assert_true(req.wants_pixels)
```

</details>

#### applies lifecycle changes through one helper

- Verify: applies lifecycle changes through one helper
   - Expected: compositor.surfaces[0].x equals `10)  # oracle: pinned constant asserted by this scenario`
   - Expected: compositor.surfaces[0].width equals `80)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-014 REQ-WEB-BROWSER-016
step("Verify: applies lifecycle changes through one helper")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var compositor = Compositor.with_backends(ApplierBackend(w: 200, h: 120), nil, 200, 120)
val created = apply_wm_action_to_compositor(compositor, _action("create_window", 0))
compositor = created.compositor
val wid = created.window_id
compositor = apply_wm_action_to_compositor(compositor, _action("move", wid)).compositor
compositor = apply_wm_action_to_compositor(compositor, _action("resize", wid)).compositor
expect(compositor.surfaces[0].x).to_equal(10)  # oracle: pinned constant asserted by this scenario
expect(compositor.surfaces[0].width).to_equal(80)  # oracle: pinned constant asserted by this scenario
compositor = apply_wm_action_to_compositor(compositor, _action("minimize", wid)).compositor
assert_false(compositor.surfaces[0].visible)
compositor = apply_wm_action_to_compositor(compositor, _action("restore", wid)).compositor
assert_true(compositor.surfaces[0].visible)
```

</details>

#### rejects every non-create action for an unknown window

- Verify: rejects every non-create action for an unknown window
   - Expected: result.window_id equals `unknown_id`
   - Expected: result.compositor.surfaces.len() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-014 REQ-WEB-BROWSER-016
step("Verify: rejects every non-create action for an unknown window")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val compositor = Compositor.with_backends(
    ApplierBackend(w: 200, h: 120), nil, 200, 120
)
val unknown_id = 999u64
val actions = [
    "destroy_window", "focus", "resize", "move", "set_title",
    "minimize", "maximize", "restore", "update_tree"
]
for kind in actions:
    val result = apply_wm_action_to_compositor(
        compositor, _action(kind, unknown_id)
    )
    expect(result.applied).to_be(false)
    expect(result.window_id).to_equal(unknown_id)
    expect(result.compositor.surfaces.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### classifies shared lifecycle actions

- Verify: classifies shared lifecycle actions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-014 REQ-WEB-BROWSER-016
step("Verify: classifies shared lifecycle actions")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
assert_true(wm_action_is_shared_lifecycle("resize"))
val none_is_lifecycle = wm_action_is_shared_lifecycle("none")
assert_false(none_is_lifecycle)
```

</details>

#### normalizes action app identity without changing lifecycle fields

- Verify: normalizes action app identity without changing lifecycle fields
   - Expected: normalized.kind equals `create_window`
   - Expected: normalized.title equals `action.title`
   - Expected: normalized.width equals `action.width`
   - Expected: normalized.owner_port equals `action.owner_port`
   - Expected: normalized.src_port equals `action.src_port`
   - Expected: normalized.app_id equals `launcher.app`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-014 REQ-WEB-BROWSER-016
step("Verify: normalizes action app identity without changing lifecycle fields")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val action = _action("create_window", 0)
val normalized = wm_action_with_app_id(action, "launcher.app")
expect(normalized.kind).to_equal("create_window")
expect(normalized.title).to_equal(action.title)
expect(normalized.width).to_equal(action.width)
expect(normalized.owner_port).to_equal(action.owner_port)
expect(normalized.src_port).to_equal(action.src_port)
expect(normalized.app_id).to_equal("launcher.app")
```

</details>

#### builds remote update trees through shared compositor logic

- Verify: builds remote update trees through shared compositor logic
   - Expected: compositor.surfaces[0].content_html equals ``
   - Expected: compositor.surfaces[0].content_revision equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: tree.root_id equals `remote_{created.window_id}`
   - Expected: "missing GUI tree" equals `present GUI tree`
   - Expected: tree.root_id equals `remote_44`
   - Expected: tree.title() equals `Window 44`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-014 REQ-WEB-BROWSER-016
step("Verify: builds remote update trees through shared compositor logic")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var compositor = Compositor.with_backends(ApplierBackend(w: 200, h: 120), nil, 200, 120)
val created = apply_wm_action_to_compositor(compositor, _action("create_window", 0))
compositor = created.compositor
val updated = apply_wm_action_to_compositor(compositor, _action("update_tree", created.window_id))
compositor = updated.compositor
assert_true(updated.applied)
expect(compositor.surfaces[0].content_kind).to_equal(
    WM_CONTENT_KIND_GUI_SESSION
)
expect(compositor.surfaces[0].content_handle).to_be_greater_than(0)
expect(compositor.surfaces[0].content_html).to_equal("")
expect(compositor.surfaces[0].content_revision).to_equal(3)  # oracle: pinned constant asserted by this scenario
if val tree = compositor.gui_content_tree(
    compositor.surfaces[0].content_handle
):
    expect(tree.root_id).to_equal("remote_{created.window_id}")
else:
    expect("missing GUI tree").to_equal("present GUI tree")

val tree = wm_action_remote_tree(44, "payload")
expect(tree.root_id).to_equal("remote_44")
expect(tree.title()).to_equal("Window 44")
```

</details>

#### builds shared lifecycle actions from host bridge requests

- Verify: builds shared lifecycle actions from host bridge requests
   - Expected: create.kind equals `create_window`
   - Expected: create.owner_port equals `42)  # oracle: pinned constant asserted by this scenario`
   - Expected: create.process_id equals `700)  # oracle: pinned constant asserted by this scenario`
   - Expected: create.app_id equals `/host/app`
   - Expected: create_web.kind equals `create_web_window`
   - Expected: create_web.content equals `https://example.test`
   - Expected: move_action.kind equals `move`
   - Expected: move_action.x equals `30)  # oracle: pinned constant asserted by this scenario`
   - Expected: resize.kind equals `resize`
   - Expected: resize.width equals `320)  # oracle: pinned constant asserted by this scenario`
   - Expected: title.kind equals `set_title`
   - Expected: title.title equals `Renamed`
   - Expected: update.kind equals `update_tree`
   - Expected: update.content equals `tree`
   - Expected: minimized.kind equals `minimize`
   - Expected: restored.kind equals `restore`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: builds shared lifecycle actions from host bridge requests")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val create = wm_action_from_bridge_request(42, COMP_CREATE_WINDOW.to_i64(), 0, "Host App", 12, 18, 240, 160, "initial", 700, "/host/app")
expect(create.kind).to_equal("create_window")
expect(create.owner_port).to_equal(42)  # oracle: pinned constant asserted by this scenario
expect(create.process_id).to_equal(700)  # oracle: pinned constant asserted by this scenario
expect(create.app_id).to_equal("/host/app")
val create_web = wm_action_from_bridge_request(42, COMP_CREATE_WEB_WINDOW.to_i64(), 0, "https://example.test", 12, 18, 240, 160, "https://example.test", 700, "/host/browser")
expect(create_web.kind).to_equal("create_web_window")
expect(create_web.content).to_equal("https://example.test")

val move_action = wm_action_from_bridge_request(42, COMP_MOVE.to_i64(), 9, "", 30, 40, 0, 0, "", 0, "")
val resize = wm_action_from_bridge_request(42, COMP_RESIZE.to_i64(), 9, "", 0, 0, 320, 220, "", 0, "")
val title = wm_action_from_bridge_request(42, COMP_SET_TITLE.to_i64(), 9, "Renamed", 0, 0, 0, 0, "", 0, "")
val update = wm_action_from_bridge_request(42, COMP_UPDATE_TREE.to_i64(), 9, "", 0, 0, 0, 0, "tree", 0, "")
val minimized = wm_action_from_bridge_request(42, COMP_MINIMIZE.to_i64(), 9, "", 0, 0, 0, 0, "", 0, "")
val restored = wm_action_from_bridge_request(42, COMP_RESTORE.to_i64(), 9, "", 0, 0, 0, 0, "", 0, "")

expect(move_action.kind).to_equal("move")
expect(move_action.x).to_equal(30)  # oracle: pinned constant asserted by this scenario
expect(resize.kind).to_equal("resize")
expect(resize.width).to_equal(320)  # oracle: pinned constant asserted by this scenario
expect(title.kind).to_equal("set_title")
expect(title.title).to_equal("Renamed")
expect(update.kind).to_equal("update_tree")
expect(update.content).to_equal("tree")
expect(minimized.kind).to_equal("minimize")
expect(restored.kind).to_equal("restore")
```

</details>

#### rejects every cross-owner remote lifecycle action

- Verify: rejects every cross-owner remote lifecycle action
   - Expected: result.windows.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: result.windows[0].owner_port equals `11)  # oracle: pinned constant asserted by this scenario`
   - Expected: result.windows[0].title equals `Owned`
   - Expected: result.windows[0].content equals `original`
   - Expected: result.windows[0].x equals `10)  # oracle: pinned constant asserted by this scenario`
   - Expected: result.windows[0].y equals `20)  # oracle: pinned constant asserted by this scenario`
   - Expected: result.windows[0].w equals `80)  # oracle: pinned constant asserted by this scenario`
   - Expected: result.windows[0].h equals `60)  # oracle: pinned constant asserted by this scenario`
   - Expected: denied.compositor.surfaces[0].content_html equals `original`
   - Expected: denied_create.windows.len() equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 57 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-014 REQ-WEB-BROWSER-016
step("Verify: rejects every cross-owner remote lifecycle action")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val create = wm_action_from_bridge_request(
    11, COMP_CREATE_WINDOW.to_i64(), 0, "Owned", 10, 20, 80, 60,
    "original", 7, "app.owner"
)
var result = apply_wm_action_to_lifecycle_windows(
    [], 1, 640, 480, create
)
val window_id = result.window_id
val attacks = [
    wm_action_from_bridge_request(22, COMP_DESTROY_WINDOW.to_i64(), window_id, "", 0, 0, 0, 0, "", 0, ""),
    wm_action_from_bridge_request(22, COMP_UPDATE_TREE.to_i64(), window_id, "", 0, 0, 0, 0, "forged", 0, ""),
    wm_action_from_bridge_request(22, COMP_FOCUS.to_i64(), window_id, "", 0, 0, 0, 0, "", 0, ""),
    wm_action_from_bridge_request(22, COMP_RESIZE.to_i64(), window_id, "", 0, 0, 300, 200, "", 0, ""),
    wm_action_from_bridge_request(22, COMP_MOVE.to_i64(), window_id, "", 90, 100, 0, 0, "", 0, ""),
    wm_action_from_bridge_request(22, COMP_SET_TITLE.to_i64(), window_id, "Forged", 0, 0, 0, 0, "", 0, ""),
    wm_action_from_bridge_request(22, COMP_MINIMIZE.to_i64(), window_id, "", 0, 0, 0, 0, "", 0, ""),
    wm_action_from_bridge_request(22, COMP_MAXIMIZE.to_i64(), window_id, "", 0, 0, 0, 0, "", 0, ""),
    wm_action_from_bridge_request(22, COMP_RESTORE.to_i64(), window_id, "", 0, 0, 0, 0, "", 0, "")
]
for attack in attacks:
    result = apply_wm_action_to_lifecycle_windows(
        result.windows, result.next_window_id, 640, 480, attack
    )
    expect(result.applied).to_be(false)
    expect(result.windows.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
    expect(result.windows[0].owner_port).to_equal(11)  # oracle: pinned constant asserted by this scenario
    expect(result.windows[0].title).to_equal("Owned")
    expect(result.windows[0].content).to_equal("original")
    expect(result.windows[0].x).to_equal(10)  # oracle: pinned constant asserted by this scenario
    expect(result.windows[0].y).to_equal(20)  # oracle: pinned constant asserted by this scenario
    expect(result.windows[0].w).to_equal(80)  # oracle: pinned constant asserted by this scenario
    expect(result.windows[0].h).to_equal(60)  # oracle: pinned constant asserted by this scenario
    expect(result.windows[0].minimized).to_be(false)

val compositor = Compositor.with_backends(
    ApplierBackend(w: 200, h: 120), nil, 200, 120
)
val created = apply_wm_action_to_compositor(compositor, create)
val denied = apply_wm_action_to_compositor(
    created.compositor, attacks[1]
)
expect(denied.applied).to_be(false)
expect(denied.compositor.surfaces[0].content_html).to_equal("original")

val forged_create = WmAction(
    kind: "create_window", window_id: 0, title: "Forged",
    x: 0, y: 0, width: 80, height: 60, content: "",
    process_id: 7, app_id: "app.forged", owner_port: 11, src_port: 22
)
val denied_create = apply_wm_action_to_lifecycle_windows(
    result.windows, result.next_window_id, 640, 480, forged_create
)
expect(denied_create.applied).to_be(false)
expect(denied_create.windows.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### applies lifecycle actions to host-neutral window state

- Verify: applies lifecycle actions to host-neutral window state
   - Expected: result.window_id equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: result.next_window_id equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].x equals `40)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].y equals `50)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].w equals `320)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].h equals `220)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].x equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].y equals `48)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].w equals `640)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].h equals `376)  # oracle: pinned constant asserted by this scenario`
   - Expected: result.windows.len() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-014 REQ-WEB-BROWSER-016
step("Verify: applies lifecycle actions to host-neutral window state")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var windows: [WmLifecycleWindowState] = []
var result = apply_wm_action_to_lifecycle_windows(windows, 1, 640, 480, _action("create_window", 0))
windows = result.windows
assert_true(result.applied)
expect(result.window_id).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(result.next_window_id).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(windows.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
assert_true(windows[0].focused)

result = apply_wm_action_to_lifecycle_windows(windows, result.next_window_id, 640, 480, wm_move_action(1, 40, 50))
windows = result.windows
expect(windows[0].x).to_equal(40)  # oracle: pinned constant asserted by this scenario
expect(windows[0].y).to_equal(50)  # oracle: pinned constant asserted by this scenario

result = apply_wm_action_to_lifecycle_windows(windows, result.next_window_id, 640, 480, wm_resize_action(1, 320, 220))
windows = result.windows
expect(windows[0].w).to_equal(320)  # oracle: pinned constant asserted by this scenario
expect(windows[0].h).to_equal(220)  # oracle: pinned constant asserted by this scenario

result = apply_wm_action_to_lifecycle_windows(windows, result.next_window_id, 640, 480, wm_focus_action(1))
windows = result.windows
assert_true(windows[0].focused)

result = apply_wm_action_to_lifecycle_windows(windows, result.next_window_id, 640, 480, _action("maximize", 1))
windows = result.windows
expect(windows[0].x).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(windows[0].y).to_equal(48)  # oracle: pinned constant asserted by this scenario
expect(windows[0].w).to_equal(640)  # oracle: pinned constant asserted by this scenario
expect(windows[0].h).to_equal(376)  # oracle: pinned constant asserted by this scenario

result = apply_wm_action_to_lifecycle_windows(windows, result.next_window_id, 640, 480, wm_destroy_action(1))
expect(result.windows.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### keeps one focused top window across minimize restore maximize and destroy

- Verify: keeps one focused top window across minimize restore maximize and destroy
   - Expected: windows[0].id equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[1].id equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].id equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[1].id equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].id equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[1].id equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].id equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[1].id equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[1].x equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[1].y equals `48)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].id equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-014 REQ-WEB-BROWSER-016
step("Verify: keeps one focused top window across minimize restore maximize and destroy")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var windows: [WmLifecycleWindowState] = []
var result = apply_wm_action_to_lifecycle_windows(windows, 1, 640, 480, _action("create_window", 0))
windows = result.windows
result = apply_wm_action_to_lifecycle_windows(windows, result.next_window_id, 640, 480, _action("create_window", 0))
windows = result.windows
expect(windows[0].id).to_equal(1)  # oracle: pinned constant asserted by this scenario
assert_false(windows[0].focused)
expect(windows[1].id).to_equal(2)  # oracle: pinned constant asserted by this scenario
assert_true(windows[1].focused)

result = apply_wm_action_to_lifecycle_windows(windows, result.next_window_id, 640, 480, _action("minimize", 2))
windows = result.windows
expect(windows[0].id).to_equal(2)  # oracle: pinned constant asserted by this scenario
assert_true(windows[0].minimized)
assert_false(windows[0].focused)
expect(windows[1].id).to_equal(1)  # oracle: pinned constant asserted by this scenario
assert_true(windows[1].focused)

result = apply_wm_action_to_lifecycle_windows(windows, result.next_window_id, 640, 480, _action("restore", 2))
windows = result.windows
expect(windows[0].id).to_equal(1)  # oracle: pinned constant asserted by this scenario
assert_false(windows[0].focused)
expect(windows[1].id).to_equal(2)  # oracle: pinned constant asserted by this scenario
assert_false(windows[1].minimized)
assert_true(windows[1].focused)

result = apply_wm_action_to_lifecycle_windows(windows, result.next_window_id, 640, 480, _action("maximize", 1))
windows = result.windows
expect(windows[0].id).to_equal(2)  # oracle: pinned constant asserted by this scenario
assert_false(windows[0].focused)
expect(windows[1].id).to_equal(1)  # oracle: pinned constant asserted by this scenario
assert_true(windows[1].focused)
expect(windows[1].x).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(windows[1].y).to_equal(48)  # oracle: pinned constant asserted by this scenario

result = apply_wm_action_to_lifecycle_windows(windows, result.next_window_id, 640, 480, wm_destroy_action(1))
windows = result.windows
expect(windows.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(windows[0].id).to_equal(2)  # oracle: pinned constant asserted by this scenario
assert_true(windows[0].focused)
```

</details>

#### restores exact pre-maximize geometry via a directly-constructed WmAction

- Verify: restores exact pre-maximize geometry via a directly-constructed WmAction
   - Expected: windows[0].x equals `10)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].y equals `20)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].w equals `80)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].h equals `60)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].x equals `10)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].y equals `20)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].w equals `80)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].h equals `60)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].x equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].y equals `48)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].w equals `640)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].h equals `376)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].restore_x equals `10)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].restore_y equals `20)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].restore_w equals `80)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].restore_h equals `60)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].x equals `10)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].y equals `20)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].w equals `80)  # oracle: pinned constant asserted by this scenario`
   - Expected: windows[0].h equals `60)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-014 REQ-WEB-BROWSER-016
step("Verify: restores exact pre-maximize geometry via a directly-constructed WmAction")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# Regression spec for
# doc/08_tracking/bug/wm_lifecycle_restore_action_does_not_restore_geometry_2026-08-08.md.
# apply_bridge_request intercepts COMP_MAXIMIZE/COMP_RESTORE before they
# ever reach apply_wm_action_to_lifecycle_windows, so this constructs
# WmAction(kind: "maximize"/"restore", ...) directly to exercise the
# lifecycle path a future direct caller would hit.
var windows: [WmLifecycleWindowState] = []
var result = apply_wm_action_to_lifecycle_windows(windows, 1, 640, 480, _action("create_window", 0))
windows = result.windows
expect(windows[0].x).to_equal(10)  # oracle: pinned constant asserted by this scenario
expect(windows[0].y).to_equal(20)  # oracle: pinned constant asserted by this scenario
expect(windows[0].w).to_equal(80)  # oracle: pinned constant asserted by this scenario
expect(windows[0].h).to_equal(60)  # oracle: pinned constant asserted by this scenario
assert_false(windows[0].maximized)

# (b) restore when never maximized is a no-op on geometry/maximized.
result = apply_wm_action_to_lifecycle_windows(windows, result.next_window_id, 640, 480, WmAction(kind: "restore", window_id: 1, title: "", x: 0, y: 0, width: 0, height: 0, content: "", process_id: 0, app_id: "", owner_port: 0, src_port: 0))
windows = result.windows
expect(windows[0].x).to_equal(10)  # oracle: pinned constant asserted by this scenario
expect(windows[0].y).to_equal(20)  # oracle: pinned constant asserted by this scenario
expect(windows[0].w).to_equal(80)  # oracle: pinned constant asserted by this scenario
expect(windows[0].h).to_equal(60)  # oracle: pinned constant asserted by this scenario
assert_false(windows[0].maximized)

# (a) maximize snapshots pre-maximize geometry into restore_x/y/w/h.
result = apply_wm_action_to_lifecycle_windows(windows, result.next_window_id, 640, 480, WmAction(kind: "maximize", window_id: 1, title: "", x: 0, y: 0, width: 0, height: 0, content: "", process_id: 0, app_id: "", owner_port: 0, src_port: 0))
windows = result.windows
assert_true(windows[0].maximized)
expect(windows[0].x).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(windows[0].y).to_equal(48)  # oracle: pinned constant asserted by this scenario
expect(windows[0].w).to_equal(640)  # oracle: pinned constant asserted by this scenario
expect(windows[0].h).to_equal(376)  # oracle: pinned constant asserted by this scenario
expect(windows[0].restore_x).to_equal(10)  # oracle: pinned constant asserted by this scenario
expect(windows[0].restore_y).to_equal(20)  # oracle: pinned constant asserted by this scenario
expect(windows[0].restore_w).to_equal(80)  # oracle: pinned constant asserted by this scenario
expect(windows[0].restore_h).to_equal(60)  # oracle: pinned constant asserted by this scenario

# (a) restore returns the exact original geometry and clears maximized.
result = apply_wm_action_to_lifecycle_windows(windows, result.next_window_id, 640, 480, WmAction(kind: "restore", window_id: 1, title: "", x: 0, y: 0, width: 0, height: 0, content: "", process_id: 0, app_id: "", owner_port: 0, src_port: 0))
windows = result.windows
assert_false(windows[0].maximized)
expect(windows[0].x).to_equal(10)  # oracle: pinned constant asserted by this scenario
expect(windows[0].y).to_equal(20)  # oracle: pinned constant asserted by this scenario
expect(windows[0].w).to_equal(80)  # oracle: pinned constant asserted by this scenario
expect(windows[0].h).to_equal(60)  # oracle: pinned constant asserted by this scenario
```

</details>

#### derives modern motion phases from lifecycle actions and window state

- Verify: derives modern motion phases from lifecycle actions and window state
   - Expected: wm_lifecycle_motion_phase("create_window", window) equals `opening`
   - Expected: wm_lifecycle_motion_phase("create_web_window", window) equals `opening`
   - Expected: wm_lifecycle_motion_phase("destroy_window", window) equals `closing`
   - Expected: wm_lifecycle_motion_phase("minimize", window) equals `minimizing`
   - Expected: wm_lifecycle_motion_phase("restore", minimized) equals `restoring`
   - Expected: wm_lifecycle_motion_phase("maximize", minimized) equals `restoring`
   - Expected: wm_lifecycle_motion_phase("focus", window) equals `focused`
   - Expected: wm_lifecycle_motion_phase("move", minimized) equals `minimized`
   - Expected: contract.class_name equals `wm-window-restoring`
   - Expected: contract.duration_ms equals `240)  # oracle: pinned constant asserted by this scenario`
   - Expected: contract.reduced_duration_ms equals `80)  # oracle: pinned constant asserted by this scenario`
   - Expected: contract.easing equals `cubic-bezier(.2,.8,.2,1)`
   - Expected: contract.transform_origin equals `dock`
   - Expected: contract.dock_origin_x equals `120)  # oracle: pinned constant asserted by this scenario`
   - Expected: contract.dock_origin_y equals `248)  # oracle: pinned constant asserted by this scenario`
   - Expected: opening.easing equals `cubic-bezier(.2,.8,.2,1)`
   - Expected: opening.transform_origin equals `center`
   - Expected: closing.easing equals `cubic-bezier(.4,0,.2,1)`
   - Expected: closing.transform_origin equals `center`
   - Expected: focused.easing equals `ease`
   - Expected: focused.reduced_duration_ms equals `80)  # oracle: pinned constant asserted by this scenario`
   - Expected: idle.easing equals `ease`
   - Expected: idle.reduced_duration_ms equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: minimized_idle.class_name equals `wm-window-minimized`
   - Expected: minimized_idle.duration_ms equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: minimized_idle.reduced_duration_ms equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-014 REQ-WEB-BROWSER-016
step("Verify: derives modern motion phases from lifecycle actions and window state")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val window = WmLifecycleWindowState(id: 3, owner_port: 11, title: "Motion", x: 20, y: 60, w: 200, h: 140, content: "", process_id: 1, app_id: "/motion", minimized: false, focused: true)
val minimized = WmLifecycleWindowState(id: 4, owner_port: 11, title: "Minimized", x: 20, y: 60, w: 200, h: 140, content: "", process_id: 1, app_id: "/motion", minimized: true, focused: false)
expect(wm_lifecycle_motion_phase("create_window", window)).to_equal("opening")
expect(wm_lifecycle_motion_phase("create_web_window", window)).to_equal("opening")
expect(wm_lifecycle_motion_phase("destroy_window", window)).to_equal("closing")
expect(wm_lifecycle_motion_phase("minimize", window)).to_equal("minimizing")
expect(wm_lifecycle_motion_phase("restore", minimized)).to_equal("restoring")
expect(wm_lifecycle_motion_phase("maximize", minimized)).to_equal("restoring")
expect(wm_lifecycle_motion_phase("focus", window)).to_equal("focused")
expect(wm_lifecycle_motion_phase("move", minimized)).to_equal("minimized")
val contract = wm_lifecycle_motion_contract("restore", minimized)
val opening = wm_lifecycle_motion_contract("create_window", window)
val closing = wm_lifecycle_motion_contract("destroy_window", window)
val focused = wm_lifecycle_motion_contract("focus", window)
val idle = wm_lifecycle_motion_contract("move", window)
val minimized_idle = wm_lifecycle_motion_contract("move", minimized)
expect(contract.class_name).to_equal("wm-window-restoring")
expect(contract.duration_ms).to_equal(240)  # oracle: pinned constant asserted by this scenario
expect(contract.reduced_duration_ms).to_equal(80)  # oracle: pinned constant asserted by this scenario
assert_true(contract.can_disable)
expect(contract.easing).to_equal("cubic-bezier(.2,.8,.2,1)")
expect(contract.transform_origin).to_equal("dock")
expect(contract.dock_origin_x).to_equal(120)  # oracle: pinned constant asserted by this scenario
expect(contract.dock_origin_y).to_equal(248)  # oracle: pinned constant asserted by this scenario
expect(opening.easing).to_equal("cubic-bezier(.2,.8,.2,1)")
expect(opening.transform_origin).to_equal("center")
expect(closing.easing).to_equal("cubic-bezier(.4,0,.2,1)")
expect(closing.transform_origin).to_equal("center")
expect(focused.easing).to_equal("ease")
expect(focused.reduced_duration_ms).to_equal(80)  # oracle: pinned constant asserted by this scenario
expect(idle.easing).to_equal("ease")
expect(idle.reduced_duration_ms).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(minimized_idle.class_name).to_equal("wm-window-minimized")
expect(minimized_idle.duration_ms).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(minimized_idle.reduced_duration_ms).to_equal(0)  # oracle: pinned constant asserted by this scenario
val summary = wm_lifecycle_motion_summary("minimize", window)
expect(summary).to_contain("phase=minimizing")
expect(summary).to_contain("class=wm-window-minimizing")
expect(summary).to_contain("easing=cubic-bezier(.4,0,.2,1)")
expect(summary).to_contain("origin=dock")
expect(summary).to_contain("dock_origin=120,248")
expect(summary).to_contain("can_disable=true")
```

</details>

#### handles taskbar hit testing in host-neutral lifecycle state

- Verify: handles taskbar hit testing in host-neutral lifecycle state
   - Expected: wm_lifecycle_hit_taskbar(windows, 640, 480, first_x + (item_w / 2), dock_y + 16) equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: wm_lifecycle_hit_taskbar(windows, 640, 480, first_x + (item_w / 2), dock_y - 1) equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-014 REQ-WEB-BROWSER-016
step("Verify: handles taskbar hit testing in host-neutral lifecycle state")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val windows = [
    WmLifecycleWindowState(id: 1, owner_port: 11, title: "One", x: 20, y: 60, w: 200, h: 140, content: "", process_id: 1, app_id: "/one", minimized: false, focused: false),
    WmLifecycleWindowState(id: 2, owner_port: 22, title: "Two", x: 40, y: 80, w: 200, h: 140, content: "", process_id: 2, app_id: "/two", minimized: false, focused: true)
]
val item_w = wm_taskbar_item_width(640, windows.len())
val first_x = wm_taskbar_item_x(640, windows.len(), 0)
val dock_y = 480 - 62
expect(wm_taskbar_dock_width(640, windows.len())).to_be_less_than(640)
expect(wm_lifecycle_hit_taskbar(windows, 640, 480, first_x + (item_w / 2), dock_y + 16)).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(wm_lifecycle_hit_taskbar(windows, 640, 480, first_x + (item_w / 2), dock_y - 1)).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### moves and resizes lifecycle windows from host-neutral pointer state

- Verify: moves and resizes lifecycle windows from host-neutral pointer state
   - Expected: moved.windows[0].x equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: moved.windows[0].y equals `48)  # oracle: pinned constant asserted by this scenario`
   - Expected: grip.interaction.resize_window_id equals `7)  # oracle: pinned constant asserted by this scenario`
   - Expected: resized.windows[0].w equals `160)  # oracle: pinned constant asserted by this scenario`
   - Expected: resized.windows[0].h equals `120)  # oracle: pinned constant asserted by this scenario`
   - Expected: up.resize_window_id equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: drag_up.drag_window_id equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-014 REQ-WEB-BROWSER-016
step("Verify: moves and resizes lifecycle windows from host-neutral pointer state")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val windows = [
    WmLifecycleWindowState(id: 7, owner_port: 11, title: "Drag", x: 40, y: 70, w: 200, h: 160, content: "", process_id: 1, app_id: "/drag", minimized: false, focused: true)
]
val drag = WmPointerInteractionState(dragging: true, drag_window_id: 7, drag_offset_x: 60, drag_offset_y: 40, resizing: false, resize_window_id: 0, resize_start_x: 0, resize_start_y: 0, resize_start_w: 0, resize_start_h: 0)
val moved = wm_lifecycle_pointer_move(windows, 8, 640, 480, drag, -20, 10)
expect(moved.windows[0].x).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(moved.windows[0].y).to_equal(48)  # oracle: pinned constant asserted by this scenario

val probe = WmPointerInteractionState(dragging: false, drag_window_id: 0, drag_offset_x: 0, drag_offset_y: 0, resizing: false, resize_window_id: 0, resize_start_x: 0, resize_start_y: 0, resize_start_w: 0, resize_start_h: 0)
val grip = wm_lifecycle_pointer_move(windows, 8, 640, 480, probe, 238, 228)
expect(grip.interaction.resize_window_id).to_equal(7)  # oracle: pinned constant asserted by this scenario
val down = wm_lifecycle_left_button(grip.interaction, true)
assert_true(down.resizing)
val resized = wm_lifecycle_pointer_move(windows, 8, 640, 480, down, 0, 0)
expect(resized.windows[0].w).to_equal(160)  # oracle: pinned constant asserted by this scenario
expect(resized.windows[0].h).to_equal(120)  # oracle: pinned constant asserted by this scenario
val up = wm_lifecycle_left_button(resized.interaction, false)
assert_false(up.resizing)
expect(up.resize_window_id).to_equal(0)  # oracle: pinned constant asserted by this scenario
val dragging = WmPointerInteractionState(dragging: true, drag_window_id: 7, drag_offset_x: 60, drag_offset_y: 40, resizing: false, resize_window_id: 0, resize_start_x: 0, resize_start_y: 0, resize_start_w: 0, resize_start_h: 0)
val drag_up = wm_lifecycle_left_button(dragging, false)
assert_false(drag_up.dragging)
expect(drag_up.drag_window_id).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### does not arm resize over a minimized window's stale bottom-right corner (FIX 2)

- Verify: does not arm resize over a minimized window's stale bottom-right corner (FIX 2)
   - Expected: grip.interaction.resize_window_id equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-014 REQ-WEB-BROWSER-016
step("Verify: does not arm resize over a minimized window's stale bottom-right corner (FIX 2)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# Sibling to the click hit-test (host_compositor_left_button_at), which
# already excludes minimized windows via `not win.minimized`. The
# pointer-move resize-corner hover arm was missing that same check.
val windows = [
    WmLifecycleWindowState(id: 7, owner_port: 11, title: "Drag", x: 40, y: 70, w: 200, h: 160, content: "", process_id: 1, app_id: "/drag", minimized: true, focused: true)
]
val probe = WmPointerInteractionState(dragging: false, drag_window_id: 0, drag_offset_x: 0, drag_offset_y: 0, resizing: false, resize_window_id: 0, resize_start_x: 0, resize_start_y: 0, resize_start_w: 0, resize_start_h: 0)
# (238, 228) is inside the bottom-right 8x8 resize grip of the
# (unminimized) geometry above — see the passing case in the previous
# test, which arms resize_window_id=7 at this exact position.
val grip = wm_lifecycle_pointer_move(windows, 8, 640, 480, probe, 238, 228)
expect(grip.interaction.resize_window_id).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `af82a46156a263e298e9cd487911045a0e4d5610c98a6d6fe417aac5e45f7c93`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `af82a46156a263e298e9cd487911045a0e4d5610c98a6d6fe417aac5e45f7c93`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `af82a46156a263e298e9cd487911045a0e4d5610c98a6d6fe417aac5e45f7c93`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/compositor/wm_action_applier_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/wm_action_applier_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/wm_action_applier_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/compositor/wm_action_applier_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/wm_action_applier_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
