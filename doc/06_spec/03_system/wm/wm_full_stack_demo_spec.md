# Wm Full Stack Demo Specification

> Tests covering WM full stack demo.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Full Stack Demo Specification

## Scenarios

### WM full stack demo

#### routes normalized host events through chrome and GUI client

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes normalized host events through chrome and GUI client
- Focus the text field through desktop-to-client coordinates
- Commit text separately from the physical Ctrl shortcut
   - Expected: field.get_prop("value") equals `Simple123`
   - Expected: field.get_prop("selection_start") equals `0`
   - Expected: field.get_prop("selection_end") equals `9`
- Activate the button through the same client route
   - Expected: session.take_pending_action() equals `wm-demo.click`
   - Expected: sound.mixed_pcm_frames equals `2880`
   - Expected: sound.active_audio_handle_count() equals `0`
- Keep titlebar dragging in the WM chrome lane


<details>
<summary>Executable SSpec</summary>

Runnable source: 98 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes normalized host events through chrome and GUI client")
val tree = wm_full_stack_demo_tree("Ready", "Play sound", "")
var session = UISession.new(tree)
session.dispatch(UIEvent.Resize(480, 480))
var compositor = HostCompositor.new_headless(Size.wh(640, 600))
compositor.apply_bridge_request(
    1, 10, COMP_CREATE_WINDOW.to_i64(), 0,
    "Full Stack WM Demo", 20, 20, 488, 516, "",
    99, WM_FULL_STACK_DEMO_APP_ID
)
var router = HostGuiEventRouter.new(1)
val rects = compute_layout(tree.root_node(), 0, 0, 480, 480)

step("Focus the text field through desktop-to-client coordinates")
if val field_rect = find_rect(rects, "demo-text-field"):
    val desktop_x = 24 + field_rect.x + field_rect.w / 2
    val desktop_y = 52 + field_rect.y + field_rect.h / 2
    expect(router.route(window_event_pointer(
        1, 1, 1, WINDOW_EVENT_POINTER_MOVE,
        desktop_x.to_i64() * 1000,
        desktop_y.to_i64() * 1000, 0, 0
    ), compositor, session)).to_be(true)
    expect(router.route(window_event_pointer(
        1, 2, 2, WINDOW_EVENT_POINTER_BUTTON,
        desktop_x.to_i64() * 1000,
        desktop_y.to_i64() * 1000, WINDOW_ACTION_PRESS, 0
    ), compositor, session)).to_be(true)
    router.route(window_event_pointer(
        1, 3, 3, WINDOW_EVENT_POINTER_BUTTON,
        desktop_x.to_i64() * 1000,
        desktop_y.to_i64() * 1000, 0, 0
    ), compositor, session)
else:
    expect(false).to_be(true)

step("Commit text separately from the physical Ctrl shortcut")
var text_event = window_event_none()
text_event.kind = WINDOW_EVENT_TEXT
expect(router.route(
    text_event, compositor, session, "Simple123"
)).to_be(true)
val field = tree.find_widget("demo-text-field")
expect(field.get_prop("value")).to_equal("Simple123")
expect(router.route(window_event_key(
    1, 4, 4, 65, 30, WINDOW_ACTION_PRESS, WINDOW_MOD_CTRL
), compositor, session)).to_be(true)
expect(field.get_prop("selection_start")).to_equal("0")
expect(field.get_prop("selection_end")).to_equal("9")

step("Activate the button through the same client route")
if val button_rect = find_rect(rects, "demo-button"):
    val desktop_x = 24 + button_rect.x + button_rect.w / 2
    val desktop_y = 52 + button_rect.y + button_rect.h / 2
    router.route(window_event_pointer(
        1, 5, 5, WINDOW_EVENT_POINTER_MOVE,
        desktop_x.to_i64() * 1000,
        desktop_y.to_i64() * 1000, 0, 0
    ), compositor, session)
    router.route(window_event_pointer(
        1, 6, 6, WINDOW_EVENT_POINTER_BUTTON,
        desktop_x.to_i64() * 1000,
        desktop_y.to_i64() * 1000, WINDOW_ACTION_PRESS, 0
    ), compositor, session)
    expect(session.take_pending_action()).to_equal("wm-demo.click")
    var sound = SoundEngine.create(SoundEngineConfig.no_audio())
    expect(sound.play_ui_click()).to_be(false)
    expect(sound.mixed_pcm_frames).to_equal(2880)
    expect(sound.mixed_pcm_checksum).to_be_greater_than(0u64)
    sound.teardown()
    expect(sound.active_audio_handle_count()).to_equal(0)
    router.route(window_event_pointer(
        1, 7, 7, WINDOW_EVENT_POINTER_BUTTON,
        desktop_x.to_i64() * 1000,
        desktop_y.to_i64() * 1000, 0, 0
    ), compositor, session)
else:
    expect(false).to_be(true)

step("Keep titlebar dragging in the WM chrome lane")
val old_x = compositor.windows[0].x
val old_y = compositor.windows[0].y
router.route(window_event_pointer(
    1, 8, 8, WINDOW_EVENT_POINTER_MOVE, 40_000, 30_000, 0, 0
), compositor, session)
router.route(window_event_pointer(
    1, 9, 9, WINDOW_EVENT_POINTER_BUTTON,
    40_000, 30_000, WINDOW_ACTION_PRESS, 0
), compositor, session)
router.route(window_event_pointer(
    1, 10, 10, WINDOW_EVENT_POINTER_MOVE, 70_000, 55_000, 0, 0
), compositor, session)
router.route(window_event_pointer(
    1, 11, 11, WINDOW_EVENT_POINTER_BUTTON,
    70_000, 55_000, 0, 0
), compositor, session)
expect(compositor.windows[0].x).to_be_greater_than(old_x)
expect(compositor.windows[0].y).to_be_greater_than(old_y)
```

</details>

#### preserves normalized key and committed text until close

- preserves normalized key and committed text until close
- Create the canonical event boundary
- Inject physical key and committed UTF-8 as separate events
   - Expected: runtime.poll_event().kind equals `WINDOW_EVENT_KEY`
   - Expected: text_event.kind equals `WINDOW_EVENT_TEXT`
   - Expected: runtime.event_text(text_event.text_handle) equals `Simple123`
- Close and return event and text handles to baseline
   - Expected: runtime.destroy_window(window) equals `WINDOW_STATUS_OK`
   - Expected: runtime.events.queued_count() equals `baseline_events`
   - Expected: runtime.events.text_live_count() equals `baseline_text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves normalized key and committed text until close")
step("Create the canonical event boundary")
var runtime = SimpleWindow.headless(8, 8)
val baseline_events = runtime.events.queued_count()
val baseline_text = runtime.events.text_live_count()
val window = runtime.create_window("event-demo", 16, 16)

step("Inject physical key and committed UTF-8 as separate events")
expect(runtime.inject_window_event(window_event_key(
    window, 1, 10, 65, 30, WINDOW_ACTION_PRESS, WINDOW_MOD_CTRL
))).to_equal(WINDOW_STATUS_OK)
expect(runtime.inject_text(window, 11, "Simple123")).to_equal(
    WINDOW_STATUS_OK
)
expect(runtime.poll_event().kind).to_equal(WINDOW_EVENT_KEY)
val text_event = runtime.poll_event()
expect(text_event.kind).to_equal(WINDOW_EVENT_TEXT)
expect(runtime.event_text(text_event.text_handle)).to_equal("Simple123")
expect(runtime.release_event_text(text_event.text_handle)).to_equal(
    WINDOW_STATUS_OK
)

step("Close and return event and text handles to baseline")
expect(runtime.destroy_window(window)).to_equal(WINDOW_STATUS_OK)
expect(runtime.events.queued_count()).to_equal(baseline_events)
expect(runtime.events.text_live_count()).to_equal(baseline_text)
```

</details>

#### routes embedded 2D dragging only through left client capture

- routes embedded 2D dragging only through left client capture
- Reject stale client coordinates after a real titlebar press
- Drag through actual client capture and release outside
   - Expected: surface.rect_y equals `62`


<details>
<summary>Executable SSpec</summary>

Runnable source: 96 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes embedded 2D dragging only through left client capture")
val tree = wm_full_stack_demo_tree("Ready", "Play sound", "")
var session = UISession.new(tree)
session.dispatch(UIEvent.Resize(480, 480))
var compositor = HostCompositor.new_headless(Size.wh(640, 600))
compositor.apply_bridge_request(
    1, 10, COMP_CREATE_WINDOW.to_i64(), 0,
    "Full Stack WM Demo", 20, 20, 488, 516, "",
    99, WM_FULL_STACK_DEMO_APP_ID
)
var router = HostGuiEventRouter.new(1)
val rects = compute_layout(tree.root_node(), 0, 0, 480, 480)
var surface = WmDemo2dState.new()
if val rect = find_rect(rects, "demo-surface-2d"):
    val x = rect.x + rect.w * 30 / 240
    val y = rect.y + rect.h * 28 / 90
    expect(surface.route_widget_pointer(
        tree.root_node(), 480, 480,
        WINDOW_EVENT_POINTER_BUTTON, 1, WINDOW_ACTION_PRESS,
        true, x, y
    )).to_be(false)
    expect(surface.dragging).to_be(false)

    step("Reject stale client coordinates after a real titlebar press")
    val desktop_x = 24 + x
    val desktop_y = 52 + y
    expect(router.route(window_event_pointer(
        1, 20, 20, WINDOW_EVENT_POINTER_MOVE,
        desktop_x.to_i64() * 1000,
        desktop_y.to_i64() * 1000, 0, 0
    ), compositor, session)).to_be(true)
    router.route(window_event_pointer(
        1, 21, 21, WINDOW_EVENT_POINTER_MOVE,
        40_000, 30_000, 0, 0
    ), compositor, session)
    val titlebar_routed = router.route(window_event_pointer(
        1, 22, 22, WINDOW_EVENT_POINTER_BUTTON,
        40_000, 30_000, WINDOW_ACTION_PRESS, 0
    ), compositor, session)
    expect(titlebar_routed).to_be(false)
    expect(surface.route_widget_pointer(
        tree.root_node(), 480, 480,
        WINDOW_EVENT_POINTER_BUTTON, 0, WINDOW_ACTION_PRESS,
        titlebar_routed,
        router.last_local_x, router.last_local_y
    )).to_be(false)
    expect(surface.dragging).to_be(false)
    router.route(window_event_pointer(
        1, 23, 23, WINDOW_EVENT_POINTER_BUTTON,
        40_000, 30_000, 0, 0
    ), compositor, session)

    step("Drag through actual client capture and release outside")
    router.route(window_event_pointer(
        1, 24, 24, WINDOW_EVENT_POINTER_MOVE,
        desktop_x.to_i64() * 1000,
        desktop_y.to_i64() * 1000, 0, 0
    ), compositor, session)
    val press_routed = router.route(window_event_pointer(
        1, 25, 25, WINDOW_EVENT_POINTER_BUTTON,
        desktop_x.to_i64() * 1000,
        desktop_y.to_i64() * 1000,
        WINDOW_ACTION_PRESS, 0
    ), compositor, session)
    expect(surface.route_widget_pointer(
        tree.root_node(), 480, 480,
        WINDOW_EVENT_POINTER_BUTTON, 0, WINDOW_ACTION_PRESS,
        press_routed, router.last_local_x, router.last_local_y
    )).to_be(true)
    expect(surface.dragging).to_be(true)
    val outside_y = rect.y + rect.h + 10
    val move_routed = router.route(window_event_pointer(
        1, 26, 26, WINDOW_EVENT_POINTER_MOVE,
        desktop_x.to_i64() * 1000,
        (52 + outside_y).to_i64() * 1000, 0, 0
    ), compositor, session)
    expect(surface.route_widget_pointer(
        tree.root_node(), 480, 480,
        WINDOW_EVENT_POINTER_MOVE, 0, 0,
        move_routed, router.last_local_x, router.last_local_y
    )).to_be(true)
    expect(surface.rect_y).to_equal(62)
    val release_routed = router.route(window_event_pointer(
        1, 27, 27, WINDOW_EVENT_POINTER_BUTTON,
        40_000, 30_000, 0, 0
    ), compositor, session)
    expect(surface.route_widget_pointer(
        tree.root_node(), 480, 480,
        WINDOW_EVENT_POINTER_BUTTON, 0, 0,
        release_routed,
        router.last_local_x, router.last_local_y
    )).to_be(true)
    expect(surface.dragging).to_be(false)
else:
    expect(false).to_be(true)
```

</details>

#### composes GUI Web and 2D frames and completes WM lifecycle

- composes GUI Web and 2D frames and completes WM lifecycle
- Build the shared VBox demo and render its GUI frame
- Attach nested pixel and Simple Web content frames
- Present a non-black shared compositor frame
- Drag maximize restore minimize and restore from taskbar
   - Expected: compositor.windows[0].x equals `maximized_x`
   - Expected: compositor.windows[0].y equals `maximized_y`
   - Expected: compositor.windows[0].w equals `maximized_w`
   - Expected: compositor.windows[0].h equals `maximized_h`
   - Expected: compositor.windows[0].x equals `normal_x`
   - Expected: compositor.windows[0].y equals `normal_y`
   - Expected: compositor.windows[0].w equals `normal_w`
   - Expected: compositor.windows[0].h equals `normal_h`
- Reflow a maximized window after desktop resize and restore exactly
   - Expected: compositor.windows[0].x equals `0`
   - Expected: compositor.windows[0].y equals `48`
   - Expected: compositor.windows[0].w equals `800`
   - Expected: compositor.windows[0].h equals `596`
   - Expected: compositor.windows[0].x equals `normal_x`
   - Expected: compositor.windows[0].y equals `normal_y`
   - Expected: compositor.windows[0].w equals `normal_w`
   - Expected: compositor.windows[0].h equals `normal_h`
   - Expected: compositor.width equals `800`
   - Expected: compositor.height equals `700`
   - Expected: compositor.drag_window_id equals `0`
   - Expected: compositor.resize_window_id equals `0`
   - Expected: compositor.armed_chrome_target equals ``
   - Expected: compositor.armed_chrome_window_id equals `0`
- Close and release top and nested content ownership
   - Expected: compositor.windows.len() equals `0`
   - Expected: compositor.external_web_window_ids.len() equals `0`
   - Expected: compositor.external_web_frames.len() equals `0`
   - Expected: compositor.external_child_frames.len() equals `0`
   - Expected: compositor.native_cache_window_ids.len() equals `0`
   - Expected: compositor.native_content_caches.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 127 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("composes GUI Web and 2D frames and completes WM lifecycle")
step("Build the shared VBox demo and render its GUI frame")
val tree = wm_full_stack_demo_tree("Ready", "Play sound", "")
var session = UISession.new(tree)
session.dispatch(UIEvent.Resize(480, 480))
val image = engine2d_resolved_draw_ir_image(
    WM_FULL_STACK_DEMO_IMAGE_URI, 2, 2,
    [0xffffcc00u32, 0xff00ccffu32, 0xff00ccffu32, 0xffffcc00u32]
)
var compositor = HostCompositor.new_headless(Size.wh(640, 600))
compositor.apply_bridge_request(
    1, 10, COMP_CREATE_WINDOW.to_i64(), 0,
    "Full Stack WM Demo", 20, 20, 488, 516, "",
    99, WM_FULL_STACK_DEMO_APP_ID
)
expect(compositor.require_external_web_frame(1)).to_be(true)
val gui_frame = gui_session_content_frame(
    session, "1", "", 0, 0, 480, 480, 1, 1, [image]
)
expect(compositor.set_external_web_frame(1, gui_frame)).to_be(true)

step("Attach nested pixel and Simple Web content frames")
val rects = compute_layout(tree.root_node(), 0, 0, 480, 480)
if val rect_2d = find_rect(rects, "demo-surface-2d"):
    val pixels = _solid(rect_2d.w, rect_2d.h, 0xff15304au32)
    val frame = pixel_surface_content_frame(
        "demo-2d", "1", rect_2d.x, rect_2d.y,
        rect_2d.w, rect_2d.h, pixels, 1, 1
    )
    expect(compositor.set_external_child_frame(frame)).to_be(true)
else:
    expect(false).to_be(true)
if val rect_web = find_rect(rects, "demo-surface-web"):
    var cache = web_render_pixel_artifact_cache(
        rect_web.w, rect_web.h, "software"
    )
    val web = simple_web_child_content_frame_cached(
        cache, "demo-web", "1", rect_web.x, rect_web.y,
        1, 1, default_theme_id(), "Embedded Web",
        "<p>Simple Web panel</p>", rect_web.w, rect_web.h, 0
    )
    expect(compositor.set_external_child_frame(web)).to_be(true)
else:
    expect(false).to_be(true)

step("Present a non-black shared compositor frame")
compositor.render_frame()
expect(_non_black(compositor.pure_simple_pixel_buffer())).to_be_greater_than(100)

step("Drag maximize restore minimize and restore from taskbar")
compositor.handle_mouse_move(40, 46)
compositor.handle_left_button(true)
expect(compositor.dragging).to_be(true)
compositor.handle_mouse_move(70, 71)
compositor.handle_left_button(false)
val normal_x = compositor.windows[0].x
val normal_y = compositor.windows[0].y
val normal_w = compositor.windows[0].w
val normal_h = compositor.windows[0].h
compositor.maximize_window(1)
expect(compositor.windows[0].maximized).to_be(true)
val maximized_x = compositor.windows[0].x
val maximized_y = compositor.windows[0].y
val maximized_w = compositor.windows[0].w
val maximized_h = compositor.windows[0].h
compositor.apply_bridge_request(
    2, 0, COMP_MINIMIZE.to_i64(), 1,
    "", 0, 0, 0, 0, "", 0, ""
)
compositor.restore_window(1)
expect(compositor.windows[0].maximized).to_be(true)
expect(compositor.windows[0].x).to_equal(maximized_x)
expect(compositor.windows[0].y).to_equal(maximized_y)
expect(compositor.windows[0].w).to_equal(maximized_w)
expect(compositor.windows[0].h).to_equal(maximized_h)
compositor.restore_window(1)
expect(compositor.windows[0].maximized).to_be(false)
expect(compositor.windows[0].x).to_equal(normal_x)
expect(compositor.windows[0].y).to_equal(normal_y)
expect(compositor.windows[0].w).to_equal(normal_w)
expect(compositor.windows[0].h).to_equal(normal_h)

step("Reflow a maximized window after desktop resize and restore exactly")
compositor.maximize_window(1)
compositor.resize(800, 700)
expect(compositor.windows[0].x).to_equal(0)
expect(compositor.windows[0].y).to_equal(48)
expect(compositor.windows[0].w).to_equal(800)
expect(compositor.windows[0].h).to_equal(596)
compositor.restore_window(1)
expect(compositor.windows[0].x).to_equal(normal_x)
expect(compositor.windows[0].y).to_equal(normal_y)
expect(compositor.windows[0].w).to_equal(normal_w)
expect(compositor.windows[0].h).to_equal(normal_h)
compositor.resize(100000, 100000)
expect(compositor.width).to_equal(800)
expect(compositor.height).to_equal(700)

compositor.dragging = true
compositor.drag_window_id = 1
compositor.resizing = true
compositor.resize_window_id = 1
compositor.armed_chrome_target = "close"
compositor.armed_chrome_window_id = 1
compositor = host_compositor_minimize_focused(compositor)
expect(compositor.windows[0].minimized).to_be(true)
expect(compositor.dragging).to_be(false)
expect(compositor.drag_window_id).to_equal(0)
expect(compositor.resizing).to_be(false)
expect(compositor.resize_window_id).to_equal(0)
expect(compositor.armed_chrome_target).to_equal("")
expect(compositor.armed_chrome_window_id).to_equal(0)
compositor.handle_mouse_move(22, 572)
compositor.handle_left_button(true)
compositor.handle_left_button(false)
expect(compositor.windows[0].minimized).to_be(false)

step("Close and release top and nested content ownership")
compositor.destroy_window(1)
expect(compositor.windows.len()).to_equal(0)
expect(compositor.external_web_window_ids.len()).to_equal(0)
expect(compositor.external_web_frames.len()).to_equal(0)
expect(compositor.external_child_frames.len()).to_equal(0)
expect(compositor.native_cache_window_ids.len()).to_equal(0)
expect(compositor.native_content_caches.len()).to_equal(0)
expect(compositor.dragging).to_be(false)
```

</details>

#### persists stable app_id pin and unpin state

- persists stable app_id pin and unpin state
- Seed the fresh demo launcher before mirroring it to the compositor
   - Expected: compositor.take_pending_taskbar_launch_app_id() equals ``
   - Expected: compositor.hit_taskbar(22, 200) equals `window_id`
- Close and reopen through the pinned stable app_id
   - Expected: compositor.windows.len() equals `0`
   - Expected: reopened_app_id equals `WM_FULL_STACK_DEMO_APP_ID`
   - Expected: compositor.windows.len() equals `1`
- Unpin by app_id and reconstruct the runtime
   - Expected: compositor.taskbar_model().pinned.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 93 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("persists stable app_id pin and unpin state")
step("Seed the fresh demo launcher before mirroring it to the compositor")
host_taskbar_runtime_clear_persisted_layout()
host_taskbar_runtime_reset()
expect(host_taskbar_runtime_try_pin_app(
    WM_FULL_STACK_DEMO_APP_ID, "WM Demo", "demo"
)).to_be(true)
host_taskbar_runtime_reset()
expect(_contains_app(
    host_taskbar_runtime_pinned_apps(), WM_FULL_STACK_DEMO_APP_ID
)).to_be(true)
var compositor = HostCompositor.new_headless(Size.wh(320, 240))
expect(compositor.pin_taskbar_app(
    WM_FULL_STACK_DEMO_APP_ID, "WM Demo", "demo"
)).to_be(true)
expect(compositor.taskbar_model().pinned[0].app_id).to_equal(
    WM_FULL_STACK_DEMO_APP_ID
)
compositor.handle_mouse_move(22, 200)
compositor.handle_left_button(true)
compositor.handle_left_button(false)
expect(compositor.take_pending_taskbar_launch_app_id()).to_equal(
    WM_FULL_STACK_DEMO_APP_ID
)
expect(compositor.take_pending_taskbar_launch_app_id()).to_equal("")
expect(compositor.pin_taskbar_app(
    "/sys/apps/second", "Second", "second"
)).to_be(true)
compositor.handle_mouse_move(100, 200)
compositor.handle_left_button(true)
compositor.handle_left_button(false)
expect(compositor.take_pending_taskbar_launch_app_id()).to_equal(
    "/sys/apps/second"
)
expect(compositor.unpin_taskbar_app(
    "/sys/apps/second"
)).to_be(true)
compositor.apply_bridge_request(
    1, 10, COMP_CREATE_WINDOW.to_i64(), 0,
    "WM Demo", 20, 20, 180, 140, "", 99,
    WM_FULL_STACK_DEMO_APP_ID
)
val window_id = compositor.windows[0].id
compositor.apply_bridge_request(
    2, 10, COMP_MINIMIZE.to_i64(), window_id,
    "", 0, 0, 0, 0, "", 99, WM_FULL_STACK_DEMO_APP_ID
)
expect(compositor.hit_taskbar(22, 200)).to_equal(window_id)
compositor.handle_mouse_move(22, 200)
compositor.handle_left_button(true)
compositor.handle_left_button(false)
expect(compositor.windows[0].minimized).to_be(false)

step("Close and reopen through the pinned stable app_id")
compositor.destroy_window(window_id)
expect(compositor.windows.len()).to_equal(0)
compositor.handle_mouse_move(22, 200)
compositor.handle_left_button(true)
compositor.handle_left_button(false)
val reopened_app_id = compositor.take_pending_taskbar_launch_app_id()
expect(reopened_app_id).to_equal(WM_FULL_STACK_DEMO_APP_ID)
compositor.apply_bridge_request(
    3, 10, COMP_CREATE_WINDOW.to_i64(), 0,
    "WM Demo", 20, 20, 180, 140, "", 99, reopened_app_id
)
expect(compositor.windows.len()).to_equal(1)
val reopened_window_id = compositor.windows[0].id
expect(reopened_window_id).to_be_greater_than(window_id)
expect(compositor.require_external_content_frame(
    reopened_window_id
)).to_be(true)
expect(compositor.windows[0].app_id).to_equal(
    WM_FULL_STACK_DEMO_APP_ID
)
compositor.maximize_window(reopened_window_id)
expect(compositor.windows[0].maximized).to_be(true)
compositor.restore_window(reopened_window_id)
expect(compositor.windows[0].maximized).to_be(false)

step("Unpin by app_id and reconstruct the runtime")
expect(host_taskbar_runtime_unpin_app(
    WM_FULL_STACK_DEMO_APP_ID
).is_ok()).to_be(true)
host_taskbar_runtime_reset()
expect(_contains_app(
    host_taskbar_runtime_pinned_apps(), WM_FULL_STACK_DEMO_APP_ID
)).to_be(false)
expect(compositor.unpin_taskbar_app(
    WM_FULL_STACK_DEMO_APP_ID
)).to_be(true)
expect(compositor.taskbar_model().pinned.len()).to_equal(0)
host_taskbar_runtime_clear_persisted_layout()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/wm/wm_full_stack_demo_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WM full stack demo.
- WM full stack demo

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-001`
- `REQ-004`
- `REQ-005`
- `REQ-007`
- `REQ-010`
- `REQ-011`
- `REQ-012`
- `REQ-014`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `34d30ccfe6f7b9b6d3d793110f0b22c06ac2c4e08ae9fdbda6f50f9f90510aad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `34d30ccfe6f7b9b6d3d793110f0b22c06ac2c4e08ae9fdbda6f50f9f90510aad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `34d30ccfe6f7b9b6d3d793110f0b22c06ac2c4e08ae9fdbda6f50f9f90510aad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/wm/wm_full_stack_demo_spec.spl
mirror: doc/06_spec/03_system/wm/wm_full_stack_demo_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/wm/wm_full_stack_demo_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/wm/wm_full_stack_demo_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/wm/wm_full_stack_demo_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 21 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/wm/wm_full_stack_demo_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 8 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/wm/wm_full_stack_demo_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes normalized host events through chrome and GUI client' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/wm/wm_full_stack_demo_spec.spl:186:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves normalized key and committed text until close' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/wm/wm_full_stack_demo_spec.spl:215:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes embedded 2D dragging only through left client capture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
