# Simple GUI Completion — GUI & Interaction Design (`release/1.0.0`)

- **Date:** 2026-11-28
- **Status:** Design Complete
- **Feature Design:** `doc/05_design/simple_gui_completion.md`

---

## 1. HiDPI Showcase Window & Dynamic Scale Change Flow (`ScreenGuiHost`)

```
+------------------------------------------------------------------+
| SimpleGui Showcase Window (macOS Cocoa / libspl_winit)           |
|  Physical Backing: dev_w x dev_h (e.g. 1600x1200 @ scale=2)      |
|  Logical Layout:   w x h         (e.g. 800x600)                  |
+------------------------------------------------------------------+
| [Toolbar: Overview | Fonts | Shapes | Scroll | Blend]  (h=22dp)  |
+-------------------------------+----------------------------------+
| Linked Scroll L (viewport=40) | Linked Scroll R (mirrored=40)    |
+-------------------------------+----------------------------------+
| Free Scroll Panel (negative control, independent offset)         |
+-------------------------------+----------------------------------+
| [Window A: alpha]             | [Window B: beta]                 |
+-------------------------------+----------------------------------+
| Event Probe (last, clicks, drag, typed, [text_input])            |
+------------------------------------------------------------------+
| [Statusbar: ready | N events]                          (h=22dp)  |
+------------------------------------------------------------------+

Display Move / ScaleFactorChanged (2.0x -> 1.0x or 1.0x -> 2.0x):
  libspl_winit ScaleFactor { scale_factor }
       │
       ▼
  GuiRenderer.poll_event() -> GUI_EVT_SCALE_CHANGED + scale_milli
       │
       ▼
  ScreenGuiHost.poll_input():
    1. scale = gui_device_scale(SIMPLE_GUI_SCALE, ev.scale_milli)
    2. (dev_w, dev_h) = g.inner_size()
    3. (w, h) = (dev_w / scale, dev_h / scale)
    4. has_retained_scene = false; retained_pixels = []
    5. emit HostInputEvent.Resize(w, h)
       │
       ▼
  showcase_core re-layouts at (w, h) -> DrawIrV3Scene ->
  raster_scene_argb_scaled(scene, dev_w, dev_h, scale) -> crisp pixels
```

---

## 2. Widget Hit-Testing, Pointer Capture & Focus Ring States

```
Z-Order Stack (Top to Bottom):
  1. Open Context Menu (overlay, anchored & clamped to canvas)
  2. Open Dropdown Popup (overlay, above/below trigger)
  3. Floating Internal Windows / Draggable Cards (sorted by z_order)
  4. Main Layout Tree (vbox / hbox / grid / fixed)

Pointer Capture State Machine (button / checkbox / dropdown / drag):
  [Idle] --pointer_down(hit_id)--> [Captured(ui_captured_id = hit_id, ui_pressed = true)]
     │                                   │
     │                          pointer_move(x, y)
     │                          (stays captured even if outside bounds)
     │                                   │
     └<--pointer_up(x, y)----------------+
          - Clear ui_captured_id & ui_pressed
          - If hit_at(x, y) == captured_id: fire click/toggle action
          - If hit_at(x, y) != captured_id: cancel activation cleanly

Focus & Blur State Machine:
  [Unfocused] --FocusNext / FocusPrev / Click(focusable)--> [Focused(focused_id)]
     - Only visible, enabled, interactive/tab_index widgets eligible
     - Prior focused widget receives ui_focus="false", preedit=""
     - New focused widget receives ui_focus="true"
  [Focused] --FocusEvent(_, "blur")-----------------------> [Unfocused(focused_id="")]
     - Clears ui_focus="false" & preedit=""
```

---

## 3. Shared WM Chrome & Glass Retained-Damage Composition

```
+------------------------------------------------------------------+
| Top Command / Menu Bar (Aqua / Aetheric / Fluid tokens)          |
+------------------------------------------------------------------+
|  +---------------------------+                                   |
|  | (x)(-) (+) Window Title   |  <- Traffic lights: x+12..64      |
|  +---------------------------+     Drag region:    x+74..w-28    |
|  | Window Body (Glass /      |                                   |
|  |  Parent-Sampling Batch)   |  <- Damage rect D expanded by     |
|  |   +-------------------+   |     causal_pad (4..32 px) on      |
|  |   | Nested Child Frame|   |     scratch backdrop, then only   |
|  |   +-------------------+   |     unpadded D committed back     |
|  +---------------------------+                                   |
+------------------------------------------------------------------+
| [Dock / Taskbar]                      [Tray] [Clock 11:15]       |
+------------------------------------------------------------------+
                                                 ▲
                                        Clock tick updates only
                                        old+new clock_rect (LOCAL)
```

---

## 4. Component Confirmation Checklist

| Component | Module | Status |
|---|---|---|
| `ScreenHost` + `RenderBackend` | `common.ui.screen_host`, `common.ui.backend` | Additive preserved (`8` `RenderBackend` importers intact) |
| Focusable Filter & Blur | `common.ui.event` | Designed (`_is_widget_focusable`, `"blur"` reset) |
| Pointer Capture | `common.ui.widget_hit` | Designed (`ui_captured_id` on press -> release-inside activation) |
| Modifier & Text Input | `GuiRenderer` + `ScreenGuiHost` | Designed (`GUI_EVT_TEXT_INPUT` + `rt_winit_event_key_shifted`) |
| Dynamic HiDPI Rescale | `ScreenGuiHost` | Designed (`GUI_EVT_SCALE_CHANGED` -> resize + cache invalidation) |
| Parent-Sampling Retained Replay | `GuiRetainedRenderSession` + `Engine2dWmFrameExecutor` | Designed (causal-pad scratch replay for glass surfaces) |
