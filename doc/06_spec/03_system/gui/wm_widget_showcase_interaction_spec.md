# WM Widget Showcase Interaction System Spec

> Pins the live hosted-widget-showcase contract: Winit events are routed into the

<!-- sdn-diagram:id=wm_widget_showcase_interaction_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_widget_showcase_interaction_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wm_widget_showcase_interaction_spec -> std
wm_widget_showcase_interaction_spec -> common
wm_widget_showcase_interaction_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_widget_showcase_interaction_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WM Widget Showcase Interaction System Spec

Pins the live hosted-widget-showcase contract: Winit events are routed into the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_widget_showcase_interaction_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Pins the live hosted-widget-showcase contract: Winit events are routed into the
shared HostCompositor state, the taskbar uses the compositor's hit geometry, and
the app fails closed when launched outside a GUI environment.

## Scenarios

### WM showcase live wrapper source contract

#### routes real Winit mouse events into the shared host compositor

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src()
expect(s).to_contain("fn apply_wm_input")
expect(s).to_contain("winit_poll_input(lp)")
expect(s).to_contain("host_compositor_pointer_move")
expect(s).to_contain("host_compositor_left_button_at")
expect(s).to_contain("input.click_buttons")
expect(s).to_contain("input.click_pressed")
expect(s).to_contain("[wm-showcase] input left_button")
```

</details>

#### does not discard events inside render_and_present

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src()
val render_pos = s.index_of("fn render_and_present")
val input_pos = s.index_of("fn apply_wm_input")
expect(render_pos >= 0).to_equal(true)
expect(input_pos > render_pos).to_equal(true)
val render_body = s.substring(render_pos, input_pos)
expect(render_body.contains("winit_poll_input")).to_equal(false)
```

</details>

#### draws the taskbar from the shared theme and host taskbar geometry

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src()
expect(s).to_contain("wm_chrome_theme()")
expect(s).to_contain("theme.taskbar")
expect(s).to_contain("theme.command_lane")
expect(s).to_contain("theme.accent")
expect(s).to_contain("theme.host_window_body")
expect(s).to_contain("theme.close_button")
expect(s).to_contain("host_taskbar_dock_width")
expect(s).to_contain("host_taskbar_item_width")
expect(s).to_contain("host_taskbar_item_x")
```

</details>

#### creates the showcase as a hosted internal window through COMP_CREATE_WINDOW

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src()
expect(s).to_contain("HostCompositor.new")
expect(s).to_contain("COMP_CREATE_WINDOW.to_i64()")
expect(s).to_contain("Widget Showcase")
expect(s).to_contain("[wm-showcase] launched app=Widget Showcase")
```

</details>

### WM showcase compositor event system

#### drags a hosted internal window by titlebar and releases cleanly

- var comp =  comp
- comp = host compositor pointer move
- comp = host compositor left button at
   - Expected: comp.dragging is true
- comp = host compositor pointer move
- comp = host compositor left button at
   - Expected: comp.dragging is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _comp()
val before_x = comp.windows[0].x
val before_y = comp.windows[0].y
comp = host_compositor_pointer_move(comp, before_x + 40, before_y + 12)
comp = host_compositor_left_button_at(comp, true, before_x + 40, before_y + 12)
expect(comp.dragging).to_equal(true)
comp = host_compositor_pointer_move(comp, before_x + 125, before_y + 78)
expect(comp.windows[0].x).to_be_greater_than(before_x)
expect(comp.windows[0].y).to_be_greater_than(before_y)
comp = host_compositor_left_button_at(comp, false, before_x + 125, before_y + 78)
expect(comp.dragging).to_equal(false)
```

</details>

#### focuses an internal window when its content area is clicked

- var comp =  two window comp
   - Expected: host_compositor_focused_window_id(comp) equals `2`
- comp = host compositor left button at
- comp = host compositor left button at
   - Expected: host_compositor_focused_window_id(comp) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _two_window_comp()
expect(host_compositor_focused_window_id(comp)).to_equal(2)
comp = host_compositor_left_button_at(comp, true, 90, 160)
comp = host_compositor_left_button_at(comp, false, 90, 160)
expect(host_compositor_focused_window_id(comp)).to_equal(1)
```

</details>

#### closes an internal window through the visible close button

- var comp =  comp
- comp = host compositor left button at
- comp = host compositor left button at
   - Expected: comp.windows.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _comp()
val win = comp.windows[0]
comp = host_compositor_left_button_at(comp, true, win.x + win.w - 14, win.y + 12)
comp = host_compositor_left_button_at(comp, false, win.x + win.w - 14, win.y + 12)
expect(comp.windows.len()).to_equal(0)
```

</details>

#### resizes an internal window from the bottom-right grip

- var comp =  comp
- comp = host compositor pointer move
- comp = host compositor left button at
   - Expected: comp.resizing is true
- comp = host compositor pointer move
- comp = host compositor left button at
   - Expected: comp.resizing is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _comp()
val win = comp.windows[0]
comp = host_compositor_pointer_move(comp, win.x + win.w - 2, win.y + win.h - 2)
comp = host_compositor_left_button_at(comp, true, win.x + win.w - 2, win.y + win.h - 2)
expect(comp.resizing).to_equal(true)
comp = host_compositor_pointer_move(comp, win.x + win.w + 34, win.y + win.h + 28)
expect(comp.windows[0].w).to_be_greater_than(win.w)
expect(comp.windows[0].h).to_be_greater_than(win.h)
comp = host_compositor_left_button_at(comp, false, win.x + win.w + 34, win.y + win.h + 28)
expect(comp.resizing).to_equal(false)
```

</details>

#### focuses a background window through its taskbar item

- var comp =  two window comp
   - Expected: host_compositor_focused_window_id(comp) equals `2`
   - Expected: comp.hit_taskbar(cx, cy) equals `1`
- comp = host compositor left button at
- comp = host compositor left button at
   - Expected: host_compositor_focused_window_id(comp) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _two_window_comp()
expect(host_compositor_focused_window_id(comp)).to_equal(2)
val cy = H - 62 + 22
val cx = _taskbar_click_x(comp, 1)
expect(comp.hit_taskbar(cx, cy)).to_equal(1)
comp = host_compositor_left_button_at(comp, true, cx, cy)
comp = host_compositor_left_button_at(comp, false, cx, cy)
expect(host_compositor_focused_window_id(comp)).to_equal(1)
```

</details>

#### restores a minimized internal window through its taskbar item

- var comp =  two window comp
- comp = host compositor left button at
- comp = host compositor left button at
- comp = host compositor minimize focused
   - Expected: comp.windows[_index_of(comp, 1)].minimized is true
- comp = host compositor left button at
- comp = host compositor left button at
   - Expected: comp.windows[_index_of(comp, 1)].minimized is false
   - Expected: host_compositor_focused_window_id(comp) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _two_window_comp()
val cy = H - 62 + 22
val cx = _taskbar_click_x(comp, 1)
comp = host_compositor_left_button_at(comp, true, cx, cy)
comp = host_compositor_left_button_at(comp, false, cx, cy)
comp = host_compositor_minimize_focused(comp)
expect(comp.windows[_index_of(comp, 1)].minimized).to_equal(true)
comp = host_compositor_left_button_at(comp, true, cx, cy)
comp = host_compositor_left_button_at(comp, false, cx, cy)
expect(comp.windows[_index_of(comp, 1)].minimized).to_equal(false)
expect(host_compositor_focused_window_id(comp)).to_equal(1)
```

</details>

### WM showcase environment behavior

#### fails closed outside a GUI environment before creating a host window

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = process_run_timeout("bin/simple", ["run", ENTRY], 30000)
expect(result.2).to_equal(2)
expect(result.0).to_contain("[wm-showcase] error=no-gui-requested")
```

</details>

<details>
<summary>Advanced: keeps the no-GUI gate before winit_loop_new in source order</summary>

#### keeps the no-GUI gate before winit_loop_new in source order

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src()
val gate_pos = s.index_of("SIMPLE_GUI")
val loop_pos = s.index_of("winit_loop_new()")
expect(gate_pos >= 0).to_equal(true)
expect(loop_pos > gate_pos).to_equal(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
