# Simple GUI Completion — Detail Design (`release/1.0.0`)

- **Date:** 2026-11-28
- **Status:** Design Complete
- **Target Branch:** `release/1.0.0`
- **Architecture:** `doc/04_architecture/simple_gui_completion.md`

---

## 1. Slice 1 — Broken Specs, TinyGUI Cache Invalidation, Theme Cascade & Child Admission

### 1.1 Repair 4 Broken UI Specs (`REQ-SGUI-001`)
Root cause verified: `src/lib/common/ui/backend_factory.spl` and `src/lib/common/ui/app.spl` do not exist.
1. `test/01_unit/app/ui/async_default_api_spec.spl`:
   - Retarget imports to `app.ui.backend_factory.{create_backend, create_sync_backend}` and `app.ui.none.app.{HeadlessApp}` / `nogc_sync_mut.ui.session.{UISession}` / `common.ui.widget.{build_tree, label, init_state}`.
   - Exercise real `create_backend("none", 3000)`, `create_sync_backend("none", 3000)`, `UISession.new(...)`, and `HeadlessApp.new(...)` instead of nonexistent `App.from_state` / `AppConfig`.
2. `test/01_unit/app/ui/unified_app_spec.spl`:
   - Retarget to `app.ui.backend_factory.{create_backend, create_sync_backend}` and `app.ui.none.app.{HeadlessApp}` + `app.ui.none.backend.{NoneBackend}`, preserving coverage of `"none"`, `"headless"`, and unknown-mode `Err` rejection.
3. `test/03_system/gui/capability_negotiation_spec.spl`:
   - Replace `use common.ui.backend_factory.{create_backend}` with `use app.ui.backend_factory.{create_backend}` (already supports `"tui"`, `"web"`, `"none"`, `"tauri"`, and unknown-mode error).
   - Verify `NoneBackend.render_image` / `show_notification` and `TuiBackend` / `WebBackend` / `TauriBackend` `capabilities()`.
4. `test/03_system/gui/unified_app_spec.spl`:
   - Retarget `common.ui.app` / `common.ui.backend_factory` to `app.ui.none.app.{HeadlessApp}`, `app.ui.none.backend.{NoneBackend}`, `app.ui.backend_factory.{create_backend}`, and `nogc_sync_mut.ui.session.{UISession}`.
   - Preserve every lifecycle test: `minimal.ui.sdn` quit run, `demo.ui.sdn` multi-event dispatch (`FocusNext`, `InsertMode`, `NormalMode`, `Quit`) with `render_count() > 1`, nonexistent file `Err`, state inspection (`NORMAL`, `"Minimal"`, `"dark"`), and `run_single_event` focus/mode transitions.
   - Update corresponding `doc/06_spec/03_system/gui/capability_negotiation_spec.md` and `doc/06_spec/03_system/gui/unified_app_spec.md` manuals.

### 1.2 TinyGUI `metadata_valid()` Same-Length Mutation Detection (`REQ-SGUI-002`)
File: `src/lib/nogc_sync_mut/tiny/gui/state.spl`
- Add `metadata_hash: i64` field to `TinyGuiState` (initialized `0` in `bounded()`).
- Add a fast deterministic structural fingerprint `_tiny_nodes_layout_hash(nodes: [TinyGuiNode]) -> i64` mixing `id.index`, `id.generation`, `parent.index`, `parent.generation`, `class_id`, `bounds.x`, `bounds.y`, `bounds.width`, `bounds.height` — wait: to keep `direct_child_extent_y` and `child_ordinal_of` at **1 scan step** (`tiny_layout_linear_spec.spl:318` pins `extent_steps == 1`!), `_tiny_nodes_layout_hash` must NOT increment `_tiny_layout_scan_steps` and must either:
  - Option i: Track `metadata_hash` on `TinyGuiState` computed at the end of `resolved_panes` (when `indexed` is true) and checked in `metadata_valid()` ONLY if `nodes.len()` is small, OR store per-node cached `(parent_index, parent_gen, height)` inside `resolved_panes`? Wait: `tiny_layout_linear_spec.spl:318` asserts `tiny_layout_scan_steps() == 1` for `direct_child_extent_y(0)` on a 201-node tree, and `tiny_layout_scan_steps` is only incremented where we explicitly increment it! Even better: computing a quick O(n) hash in `metadata_valid()` doesn't touch `_tiny_layout_scan_steps`, OR we can add a `me set_bounds(index: i32, bounds: TinyRect)` / `me set_parent(...)` mutation API AND verify `metadata_hash == _tiny_nodes_layout_hash(self.nodes)` inside `metadata_valid()`! Wait: checking `self.metadata_hash == _tiny_nodes_layout_hash(self.nodes)` catches ALL direct public mutations to `state.nodes[i].bounds` or `state.nodes[i].parent` without modifying `_tiny_layout_scan_steps` and keeps `resolved_panes` (`601` steps) and `direct_child_extent_y` (`1` step) exact! Let's verify `TinyGuiState` has no positional constructors outside `bounded`: let's grep `TinyGuiState(` in `src/` and `test/` before editing.

### 1.3 Theme Cascade Effective Declaration & Child-Frame Admission (`REQ-SGUI-003`)
1. `src/app/ui.web/wm_quality_contract.spl`:
   - Replace `_css_var(css, name)`'s first-match `css.index_of(marker)` with an effective base-`:root` scanner `_css_var_effective(css, name)`:
     - Scans `:root {` blocks in CSS order (skipping `:root[data-wm-...]` attribute selectors and `@media (...) { :root` overrides, because base `:root {` blocks end cleanly with `\n}` or `}`).
     - Keeps the **last** matching `name: value;` declaration found across unconditional `:root { ... }` blocks, falling back to last occurrence anywhere if no `:root {` match is found.
     - Verify `glass_dark` stays within the `1700..1900` contrast band and `aetheric_dark` / `fluid_light` read their effective cascade values.
2. `src/os/compositor/host_compositor_core.spl`:
   - In `set_external_child_frame(frame: WmContentFrame) -> bool` (`:1247`), apply the same theme admission check as `_set_external_web_frame_with_ownership`:
     - When `frame.origin_kind == WM_CONTENT_ORIGIN_SIMPLE_WEB` or (`frame.origin_kind == WM_CONTENT_ORIGIN_GUI` and `frame.theme_id != ""`), or `frame.origin_kind == WM_CONTENT_ORIGIN_PIXEL_SURFACE` and `frame.theme_id != ""`, require `frame.theme_id == _host_active_content_theme_id()`.

---

## 2. Slice 2 — Focus, Blur, Pointer Capture, Modifier/Text Input, HiDPI & `HostCompositor`

### 2.1 Focus Traversal & Blur Lifecycle (`REQ-SGUI-004`)
Files: `src/lib/common/ui/event.spl`, `src/lib/common/ui/widget.spl`, `src/lib/common/ui/widget_hit.spl`
- Add helper `_is_widget_focusable(node: WidgetNode) -> bool`:
  - Returns `false` if `not node.is_visible()` or `node.get_prop("disabled") == "true"` or `node.get_prop("focusable") == "false"`.
  - If `node.get_prop("focusable") == "true"` or `node.get_prop("tab_index") != ""`, returns `true`.
  - Otherwise returns `true` for interactive widget kinds: `"button"`, `"input"`, `"textfield"`, `"textarea"`, `"checkbox"`, `"dropdown"`, `"switch"`, `"slider"`, `"tabs"`, `"list"`, `"table"`, `"tree"`, `"menubar"`, `"dialog"`, and `false` for non-interactive layout/display kinds (`"panel"`, `"text"`, `"label"`, `"heading"`, `"divider"`, `"image"`, `"progress"`, `"statusbar"`, `"tooltip"`).
- Update `get_focusable_ordered(tree: UITree) -> [text]` (`event.spl:474`):
  - Filter `ids` using `_is_widget_focusable(WidgetNode(id: id))` (with fallback: if `focus_next`/`focus_prev` finds zero filtered IDs in a tree without interactive kinds, return `[]` cleanly rather than crashing).
- Update `focus_next` / `focus_prev` and `handle_focus_event` (`event.spl:400-464`):
  - On focus transfer (`old_id -> new_id`), clear `ui_focus="false"` and `preedit=""` on `old_id` (if non-empty and different from `new_id`) and set `ui_focus="true"` on `new_id`.
  - On `handle_focus_event(state, target_id, "blur")`: if `target_id == ""` or `target_id == state.focused_id`, clear `ui_focus="false"` and `preedit=""` on `state.focused_id` and return `UIState(..., focused_id: "", ...)`.

### 2.2 Pointer Capture & Modifier/Text Input Plumbing (`REQ-SGUI-005`)
1. **Pointer Capture (`src/lib/common/ui/widget_hit.spl`):**
   - On `widget_dispatch_pointer_down`: store `root.set_prop("ui_captured_id", hit_id)` whenever a button/checkbox/dropdown/text-input (or draggable node) captures the press; defer `button` `click_count` / `ui_action_pending`?
   - **Careful backward compatibility check:** Existing `showcase_core_spec.spl` and `ui_draw_ir_pipeline_spec.spl` may test `widget_dispatch_click` or `widget_dispatch_pointer_down` directly! Let's check both specs before deciding whether `click_count` increments on `pointer_up` (when released inside `ui_captured_id`) vs `pointer_down`. If `ui_draw_ir_pipeline_spec.spl` checks `widget_set_pressed` + `widget_dispatch_click`, those are separate functions. In `widget_dispatch_pointer_down` / `widget_dispatch_pointer_up`, firing button activation on `pointer_up` when `captured_id` matches the hit at `(px, py)` (and clearing `ui_captured_id` + `ui_pressed` even when released outside) implements true pointer capture; we will inspect `showcase_core_spec.spl` to verify exact assertions on `down` vs `up`.
2. **Modifier & Text Input Plumbing (`src/lib/nogc_sync_mut/ui/gui_renderer.spl`, `src/app/ui_showcase/hosts/host_gui.spl`):**
   - `libspl_winit` ALREADY exports `rt_winit_event_key_shifted(ev)`, `rt_winit_event_text_len(ev)`, and `rt_winit_event_text_byte(ev, i)`!
   - In `GuiRenderer` (`gui_renderer.spl`):
     - Resolve `fp_key_shifted` (`rt_winit_event_key_shifted`), `fp_text_len` (`rt_winit_event_text_len`), `fp_text_byte` (`rt_winit_event_text_byte`) optionally (default `0` if older cdylib).
     - Add `GUI_EVT_TEXT_INPUT: i64 = 11` constant and export it.
     - Add `mods: i64`, `text_ch: text`, and `scale_milli: i64` fields to `GuiWindowEvent` (keeping existing field defaults/positional compat via factory helpers or named fields).
     - In `poll_event`:
       - When `ty == GUI_EVT_KEYBOARD`: read `shifted = rt_winit_event_key_shifted(ev)` -> set `mods = if shifted != 0: 1 else: 0`.
       - When `ty == GUI_EVT_TEXT_INPUT`: read UTF-8 bytes via `fp_text_len` + `fp_text_byte` into `text_ch` (and origin keycode/pressed).
       - When `ty == GUI_EVT_SCALE_CHANGED`: query `self.scale_factor_milli()` and populate `scale_milli`.
   - In `ScreenGuiHost` (`src/app/ui_showcase/hosts/host_gui.spl`):
     - `gui_event_to_host`:
       - For `GUI_EVT_TEXT_INPUT`: emit `host_key_down(winit_keycode_to_canon(ev.keycode), ev.text_ch, ev.mods)` when `ev.text_ch != ""`.
       - For `GUI_EVT_KEYBOARD`: propagate `ev.mods` (`HOST_MOD_SHIFT`) and uppercase `ch` when `mods & HOST_MOD_SHIFT != 0` (if `GUI_EVT_TEXT_INPUT` isn't used), or avoid duplicate char insertion by emitting non-printing/modified keys cleanly.

### 2.3 Dynamic HiDPI Scaling (`REQ-SGUI-006`)
Files: `src/app/ui_showcase/hosts/host_gui.spl`
- In `ScreenGuiHost.poll_input()`:
  - Handle `GUI_EVT_SCALE_CHANGED`:
    - Query `new_scale = gui_device_scale(env_get("SIMPLE_GUI_SCALE") ?? "", if ev.scale_milli > 0: ev.scale_milli else: self.g.scale_factor_milli())`.
    - Query `inner = self.g.inner_size()` (exact physical pixels!).
    - Update `self.scale = new_scale`, `self.dev_w`, `self.dev_h`, `self.w = self.dev_w / new_scale`, `self.h = self.dev_h / new_scale`.
    - Invalidate `self.has_retained_scene = false`, `self.retained_pixels = []`.
    - Return `host_resize(self.w, self.h)` so `showcase_core` re-layouts and re-renders at the new logical dimensions!
  - In `GUI_EVT_RESIZED`:
    - Preserve exact physical `inner_size()` dimensions for `self.dev_w` / `self.dev_h` rather than multiplying rounded `resize_w * self.scale`, keeping `self.w = self.dev_w / self.scale` and `self.h = self.dev_h / self.scale`.

### 2.4 `HostCompositor` Pointer & Minimize Fixes (`REQ-SGUI-010`)
File: `test/03_system/wm/wm_full_stack_demo_spec.spl` + `src/os/compositor/host_compositor_core.spl`
- Fix the 3 pre-existing `HostCompositor` pointer/minimize mismatches in `wm_full_stack_demo_spec.spl`:
  1. Lines 181-194 and 260-279: titlebar drag probe used `(40_000, 30_000)` (`x=40, y=30`), which lands inside the Aqua close button (`[win.x+12..win.x+24, win.y+8..win.y+20)` = `[32..44, 28..40)`). Move titlebar drag pointer coordinates to `(120_000, 30_000)` (`x=120` = `win.x+100`, clear of left traffic lights and right close button).
  2. Line 440: after `compositor.resize(800, 700)` (`:412`), taskbar band is `y = 644..700` (`height - 56`), not `572`. Compute taskbar click y dynamically from `compositor.height - 28` (`672`).
  3. Verify `host_compositor_minimize_focused` and `host_compositor_left_button_at` keep `dragging`/`resizing`/`armed_chrome_*` cleared on minimize and un-minimize cleanly on taskbar click.

---

## 3. Slice 3 — Retained-Damage Parent-Sampling & Release SSpec Gates

### 3.1 `GuiRetainedRenderSession.render_damage` Parent-Sampling Parity (`REQ-SGUI-007`)
File: `src/lib/gc_async_mut/ui/gui_content_renderer.spl`
- Currently, `GuiRetainedRenderSession.render_damage` (`:66-82`) dispatches non-idle plans straight to `engine2d_draw_ir_render_composition_damaged`, which rejects parent-sampling glass roots (`retained-composition-unsafe-embedding`).
- Fix:
  - Inspect `composition.batches` for parent-sampling batches (`batch.embedding.samples_parent` / style `backdrop-filter`).
  - When a non-idle `DamagePlan` (`DAMAGE_PLAN_LOCAL` or `DAMAGE_PLAN_FULL`) hits a parent-sampling root:
    - For `DAMAGE_PLAN_FULL`: re-seed via `engine2d_draw_ir_adv_composition_owner_with_images` (preserving `self.engine` ownership).
    - For `DAMAGE_PLAN_LOCAL`: route through a padded offscreen scratch replay helper (`_gui_replay_parent_sampling_damage`) mirroring `_wm_replay_parent_sampling_composition` (padded backdrop -> intersecting parent-sampling batches -> unpadded rect commit) so `GuiRetainedRenderSession` never fails closed on glass themes!

### 3.2 Showcase Stabilization & SSpec Gates (`REQ-SGUI-008`, `REQ-SGUI-009`)
- Verify `ui_showcase` hosts (`host_2d`, `host_2d_engine`, `host_gui`, `host_web`, `host_wm`, `host_tui`) compile and pass `showcase_core_spec.spl`, `showcase_hosts_spec.spl`, `showcase_event_spec.spl`.
- Add / verify SSpec system gates for:
  - `test/03_system/gui/macos_gui_live_window_evidence_spec.spl` (live macOS `SimpleGui` capture or explicit non-macOS receipt)
  - `test/03_system/gui/ui_draw_ir_pipeline_spec.spl` & `test/03_system/gui/engine2d_gpu_offload_contract_spec.spl`
  - New focused unit/system specs for focus/blur/pointer-capture/HiDPI dynamic scale/TinyGUI mutation invalidation, each with matching `doc/06_spec/` Markdown manuals (`find doc/06_spec -name '*_spec.spl' | wc -l == 0`).
