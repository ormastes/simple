# Simple GUI Completion — Local Research (2026-11)

- **Date:** 2026-11-28
- **Workspace:** `/Users/ormastes/work/web_2d_gui_gui` (branch `work/simple-gui-complete`)
- **Scope:** Source & tracking inspection only (no `native-build` or multi-spec test runs executed in this phase).
- **Sidecar status note:** `N/A` — research and open-bug verification were performed directly by inspecting workspace source files, SSpec definitions, and tracking records without spawning lower-model sidecars.

---

## 1. Knowledge Route Receipt

Matched against `doc/00_llm_process/knowledge_registry.sdn`:

| Route Type | Key / Prefix | Group ID & Doc | Expert Doc | Architecture Profile |
|---|---|---|---|---|
| Feature group (rendering/UI) | `rendering_ui` | `rendering_ui` (`doc/00_llm_process/feature_group/rendering_ui/skill.md`) | — | — |
| Layer route (longest prefix for Engine2D / Browser Engine) | `src/lib/gc_async_mut/gpu/engine2d`, `src/lib/gc_async_mut/gpu/browser_engine` | `rendering_ui` (`doc/00_llm_process/feature_group/rendering_ui/skill.md`) | `doc/00_llm_process/feature_expert/gpu_offload_check/skill.md` | `mdsoc_plus` |
| Layer route (stdlib fallback for `src/lib/common/ui`, `src/lib/gui`, `src/lib/nogc_sync_mut/ui`) | `src/lib` | `runtime_memory_io` (`doc/00_llm_process/layer_base/runtime_memory_io/skill.md`) | — | `mdsoc_plus` |
| Layer route (app fallback for `src/app/ui`, `src/app/ui_showcase`) | `src/app` | `app_editor_tooling` (`doc/00_llm_process/layer_base/app_editor_tooling/skill.md`) | — | `mdsoc_plus` |
| Layer expert (shared UI render layer) | `src/lib/common/ui/` | `rendering_ui` | `doc/00_llm_process/layer_expert/ui_render/skill.md` | `mdsoc_plus` |
| Feature expert (GUI & Vulkan/RenderDoc) | `ui_gui` | `rendering_ui` | `doc/00_llm_process/feature_expert/ui_gui/skill.md` | — |
| Feature expert (WM GUI window drawing) | `wm_gui_window_drawing` | `rendering_ui` | `doc/00_llm_process/feature_expert/wm_gui_window_drawing/skill.md` | — |

Key invariants recorded from these knowledge docs:
1. **`DrawIrV3Scene` is the shared render contract** (`ui_render/skill.md:11-12,37-39`), whereas `app.ui.render` is a text/HTML string contract.
2. **`ScreenHost` is strictly additive over `RenderBackend`** (`ui_render/skill.md:40-62`, `src/lib/common/ui/backend.spl:16-24`, `src/lib/common/ui/screen_host.spl:8-13`): `RenderBackend` keeps its 8 live importers unchanged.
3. **`WidgetNode` is a handle over a module-global store**, not a pure value (`ui_render/skill.md:63-66`, `src/app/ui_showcase/showcase_core.spl:3-7`), so tests and callers must isolate widget IDs by prefix.
4. **Device/host evidence honesty** (`rendering_ui/skill.md:12-35`, `ui_gui/skill.md:27-68`, `wm_gui_window_drawing/skill.md:265-343`): `device_readback` provenance, `GuiRenderer` SFFI cdylib (`libspl_winit`), and non-seed binary gating are mandatory on macOS live-window gates.

---

## 2. Core UI, Showcase, and Compositor Architecture Inventory

### 2.1 Backend & Host Traits (`src/lib/common/ui/`)
- **`RenderBackend`** (`src/lib/common/ui/backend.spl:32-55`): legacy `UIState` + `render_html` trait (`init`, `shutdown`, `render(state: UIState)`, `render_html(state: UIState)`, `poll_event`, `supports_*`, `viewport_*`, `backend_name`). Imported by **8 targets**:
  - `src/app/ui.tauri/backend.spl:7`
  - `src/app/ui.tui/backend.spl:6`
  - `src/app/ui.electron/backend.spl:6`
  - `src/app/ui.web/backend.spl:6`
  - `src/app/ui.vscode/backend.spl:7`
  - `src/app/ui.none/backend.spl:6`
  - `src/os/compositor/browser_backend.spl:16` (`impl RenderBackend for BrowserBackend` at `:307`)
  - `src/os/compositor/fb_backend.spl:15` (`impl RenderBackend for FramebufferBackend` at `:133`)
- **`ScreenHost`** (`src/lib/common/ui/screen_host.spl:32-46`): additive DrawIR v3 seam (`host_name`, `size`, `present_scene(DrawIrV3Scene) -> bool`, `poll_input() -> HostInputEvent?`, `shutdown`), implemented by 8 showcase host adapters:
  - `src/app/ui_showcase/hosts/host_2d.spl:107` (`Screen2dHost`)
  - `src/app/ui_showcase/hosts/host_2d_engine.spl:117` (`Screen2dEngineHost`)
  - `src/app/ui_showcase/hosts/host_2d_gpu.spl:113` (`Screen2dGpuHost`)
  - `src/app/ui_showcase/hosts/host_2d_vulkan.spl:170` (`Screen2dVulkanHost`)
  - `src/app/ui_showcase/hosts/host_gui.spl:192` (`ScreenGuiHost`)
  - `src/app/ui_showcase/hosts/host_tui.spl:440` (`ScreenTuiHost`)
  - `src/app/ui_showcase/hosts/host_web.spl:399` (`ScreenWebHost`)
  - `src/app/ui_showcase/hosts/host_wm.spl:100` (`ScreenWmHost`)

### 2.2 Widget Tree, Layout, Builders, and Interaction Lifecycle
- **Widget & State Model (`src/lib/common/ui/widget.spl:44-245`)**:
  - `UIMode` (`Normal`, `Command`, `Insert`, `Menu`) and `UIEvent` (`KeyPress`, `Resize`, `MouseEvent`, `ScrollEvent`, `FocusEvent`, `InputChange`, `DragStart/Move/Drop`, `Copy/Cut/Paste/PasteFromHistory`, `CompositionUpdate/Commit`).
  - `UITree` (`:98-211`) uses `WidgetNode` handles backed by `widget_store_ops` and a `tokens: Dict<text, text>` bag; `UIState.new` (`:229-238`) sets `focused_id` to `tree.root_id`.
- **Layout Engine (`src/lib/common/ui/layout.spl:16-543`)**:
  - `compute_pixel_layout` (`:38-39`) and `compute_layout` (`:41-62`) scale entry coordinates once via `_apply_scale(v, scale_permille)` (`:16-19`), then delegate to `_layout_scaled` (`:67-136`) so nested containers never double-scale coordinates while authored size props (`width`, `height`, `min_*`, `max_*`, `max_height`) are scaled at read sites.
  - Supports `vbox` (`:153-214`), `hbox` (`:223-291`), `grid` (`:300-386`), and `fixed` (`:415-437`) with remainder-award invariants and `clamp_dim` (`:517-525`).
- **Builders & Desktop Scene (`src/lib/common/ui/builder.spl:31-260`, `src/lib/common/ui/interactive_desktop_scene.spl:32-200`)**:
  - Fluent builders cover containers, leaf inputs, `context_menu`, `internal_window`, `draggable_card`, `z_order`, and `opacity_milli`.
  - `interactive_desktop_scene.spl` models 6 interactive desktop flows (`DesktopWindow`, `DraggableCard`, `SceneButton`, `SceneDropdown`, `SceneContextMenu`, `SceneTextField`) over `widget_tree_to_draw_ir` and `Engine2D`.
- **Event Routing & Hit-Testing (`src/lib/common/ui/event.spl:48-555`, `src/lib/common/ui/widget_hit.spl:28-868`)**:
  - `widget_dispatch_pointer_down` (`widget_hit.spl:673-742`) resolves open context menus -> open dropdown popups -> z-sorted floating windows/cards -> main laid-out rects, updating `ui_focus`, `z_order`, `ui_pressed`, and `ui_drag_node_id`.
  - **Verified gaps in widget/focus/input lifecycle:**
    1. `get_focusable_ordered` (`event.spl:474-515`) collects **every non-empty ID** from `tree.all_widget_ids()`, sorting by `tab_index` without filtering out non-focusable containers/labels, disabled nodes, or invisible nodes (`is_visible()`). By contrast, `TinyGuiState.resolved_panes` (`src/lib/nogc_sync_mut/tiny/gui/state.spl:165-169`) checks `TINY_COMPONENT_FLAG_FOCUSABLE` and `DrawIrV3HitShapeTable` (`src/lib/common/ui/draw_ir_v3.spl:185-200`) carries `z_indices`, `enableds`, and `pointer_policies`.
    2. `handle_focus_event` (`event.spl:400-411`) ignores `"blur"` events (`if kind == "blur": return state`), leaving `focused_id` stale on blur.
    3. `widget_dispatch_pointer_up` (`widget_hit.spl:775-783`) clears `ui_drag_node_id` and all `ui_pressed` flags, then hit-tests `(px, py)` at release instead of tracking pointer capture for pressed non-drag controls (e.g., triggering button action only when pointer-up lands within the captured button or delivering drag-cancel cleanly).
    4. `ScreenGuiHost` (`src/app/ui_showcase/hosts/host_gui.spl:80-108,135-143`) translates `GUI_EVT_KEYBOARD` via unshifted `gui_canon_to_ch` because `GuiWindowEvent` (`src/lib/nogc_sync_mut/ui/gui_renderer.spl:81-89`) carries no modifier mask and `poll_event` frees `GUI_EVT_TEXT_INPUT` handles without surfacing text payloads.
    5. `src/lib/gui/pure_core.spl:7-124` defines value-level `GuiInputEvent` / `GuiCommand` / `GuiDirtyRegion` / `GuiCommandBatch` for SMF dynlib hot-probe boundaries, separate from `UIEvent` / `HostInputEvent`.

### 2.3 DrawIR v3, HiDPI Device Scaling, and Native Window Facade
- **`DrawIrV3Scene`** (`src/lib/common/ui/draw_ir_v3.spl:27-200,921-962`): flat SoA side tables (`DrawIrV3GeometryTable`, `DrawIrV3PaintTable`, `DrawIrV3TextRunTable`, `DrawIrV3ResourceTable`, `DrawIrV3PathPointTable`, `DrawIrV3ClipTable`, `DrawIrV3TransformTable`, `DrawIrV3HitShapeTable` bumped to `DRAW_IR_V3_SCHEMA_ID = 4u32` with `z_indices`, `enableds`, `pointer_policies`).
- **Device Scaling (`src/lib/common/ui/draw_ir_device_scale.spl:142-207,346-466`)**: `draw_ir_composition_at_device_scale(composition, k)` scales rects, clips, points, `font-size`, `font-size-milli`, `device-advance-widths`, `device-glyph-xs`, and `pen-origin-milli` by integer `k >= 1`.
- **Native Window Facade (`src/lib/nogc_sync_mut/ui/gui_renderer.spl:68-127,218-250,450-523`)**: `GuiRenderer` dlopens `build/sffi/libspl_winit.<dylib|so|dll>` via `DynLib` + `NativeSessionOwnerV1`, exposing `inner_size()`, `scale_factor_milli()`, `poll_event()`, and `present_argb_u32()` via staging pointers (`rt_ptr_write_i64`/`i32`).
- **Showcase GUI Host (`src/app/ui_showcase/hosts/host_gui.spl:40-66,170-261` & `scene_raster.spl:47-127`)**: `ScreenGuiHost.open` reads `gui.inner_size()` and `gui.scale_factor_milli()`, computes integer `scale = gui_device_scale(...)`, lays out in logical units (`dev_w / scale`, `dev_h / scale`), and rasterizes via `raster_scene_argb_scaled` (`RasterSurface.new_scaled`).
  - **Verified HiDPI gaps:** `GuiRenderer` defines `GUI_EVT_SCALE_CHANGED = 7` (`gui_renderer.spl:74,632`), but `gui_event_to_host` (`host_gui.spl:110-146`) and `ScreenGuiHost.poll_input` (`host_gui.spl:218-255`) ignore `GUI_EVT_SCALE_CHANGED`, so moving a window between Retina and 1x external displays does not rescale or invalidate `has_retained_scene`. Additionally, `gui_device_scale` rounds fractional factors (`1.25`/`1.5`) to integers, and `GUI_EVT_RESIZED` recomputes `dev_w = resize_w * self.scale` (dropping odd device pixels under `scale >= 2`).

### 2.4 Theme & Compositor Stack
- **`SimpleTheme` -> `WmChromeColors`** (`src/lib/common/ui/simple_theme.spl:4-127`, `src/lib/common/ui/wm_chrome_theme.spl:26-128,257-331,513-539`): `SimpleTheme` resolves CSS custom properties (`--ui-bg`, `--ui-fg`, `--ui-accent`, `--app-surface`, `--app-surface-hover`, `--ui-error`) and projects them onto `WmChromeColors` (`register_wm_chrome_theme`), while `apply_theme_render_snapshot_to_wm_chrome` installs generated `ThemeRenderSnapshot` records (`src/lib/common/ui/generated/*_theme_snapshot.spl`) consumed by `widget_draw_ir.spl:84-168`, `wm_scene.spl:141-250`, and `engine2d_wm_frame_executor.spl:163`.
- **Hosted Compositor & Damage Execution (`src/os/compositor/host_compositor_entry.spl:1-6`, `engine2d_wm_frame_executor.spl:335-470,864-1150`)**: `Engine2dWmFrameExecutor.retained_scene_damage_plan` computes incremental `DAMAGE_PLAN_LOCAL` rects for clock ticks (`clock_rect` + clock-independent `taskbar_key`), window moves/resizes (old + new full bounds), and changed content frame URIs. `_wm_replay_parent_sampling_composition` handles glass/parent-sampling batches via padded offscreen scratch backdrop + unpadded damage commit.

---

## 3. Verification of Broken Specs & Open Bugs

| # | Item / Tracking File | Claimed Issue | Verified Code Status (2026-11-28) | Exact Evidence |
|---|---|---|---|---|
| 1 | 4 broken UI specs (`async_default_api_spec.spl`, `test/01_unit/app/ui/unified_app_spec.spl`, `capability_negotiation_spec.spl`, `test/03_system/gui/unified_app_spec.spl`) | Import nonexistent `common.ui.backend_factory` (and `common.ui.app`) | **OPEN (confirmed broken imports).** `src/lib/common/ui/backend_factory.spl`, `src/lib/common/ui/app.spl`, `src/lib/common/ui/__init__.spl`, `src/lib/common/ui/mod.spl` do not exist; `UnifiedApp` / `AppConfig` do not exist in `src/lib/common/ui/` or `src/app/ui*/`. Closest equivalents are `src/app/ui/backend_factory.spl:77-127` (`create_backend`), `src/app/ui.none/app.spl:19` (`HeadlessApp`), and `src/lib/nogc_sync_mut/ui/session.spl:51` (`UISession`). Fails loudly per `ui_render/skill.md:187-192`. | `test/01_unit/app/ui/async_default_api_spec.spl:1-6`, `test/01_unit/app/ui/unified_app_spec.spl:1-5`, `test/03_system/gui/capability_negotiation_spec.spl:3,30`, `test/03_system/gui/unified_app_spec.spl:2,33-34`, `src/app/ui/backend_factory.spl:22-127` |
| 2 | `doc/08_tracking/bug/tiny_gui_sibling_flow_overflow_2026-11-14.md` | i32 accumulation overflow in sibling flow & cache invalidation | **PARTIAL (source fix present, runtime verification & cache bug open).** `tiny_add_i32_saturating` is wired at all 4 sites in `src/lib/nogc_sync_mut/tiny/gui/state.spl:203,216,231-232`. Separate open defect confirmed at `state.spl:68-77`: `metadata_valid()` checks `metadata_nodes != self.nodes.len()`, so same-length in-place edits to `nodes[i].bounds` or `parent` leave stale cached metadata valid. | `src/lib/nogc_sync_mut/tiny/gui/state.spl:68-77,193-233` |
| 3 | `doc/08_tracking/bug/gui_showcase_no_hidpi_scale_half_size_glyphs_2026-10-05.md` | Drawable/frame mismatch & missing 2x scale in showcase GUI | **FIXED at startup, INCOMPLETE for runtime DPI change.** `ScreenGuiHost.open` (`host_gui.spl:178-190`) uses `inner_size()` and `gui_device_scale`, and `RasterSurface.new_scaled` (`scene_raster.spl:64-127`) scales rects/clips/glyphs. However, `GUI_EVT_SCALE_CHANGED` (`gui_renderer.spl:74`) is unhandled in `host_gui.spl:110-146,218-255`, and fractional scales (`1.25`/`1.5`) round to integer. | `src/app/ui_showcase/hosts/host_gui.spl:40-66,110-146,178-256`, `src/lib/nogc_sync_mut/ui/gui_renderer.spl:74,632` |
| 4 | `doc/08_tracking/bug/2026-11-13_ui_theme_snapshot_literal_compile_failure.md` | Giant single-line `composed_css` literal in `ThemeRenderSnapshot` fails compile | **MITIGATED in generated snapshots; runtime spec re-check needed.** `src/lib/common/ui/generated/aetheric_dark_theme_snapshot.spl:8-11` (and `fluid_dark`, `fluid_light`) now delegate `composed_css` to chunked helpers (`_aetheric_dark_composed_css()` / `_aetheric_dark_css_0()`). `ui_log_modes_spec.spl` / `src/app/ui/main.spl --help` need current-branch verification. | `src/lib/common/ui/generated/aetheric_dark_theme_snapshot.spl:8-75`, `src/app/ui/main.spl:35-51` |
| 5 | `doc/08_tracking/bug/db/gui_retained_render_session_cpu_seed_preflight_rejected_2026-11-13.sdn` | `GuiRetainedRenderSession.seed` rejected with `fresh-device-command-preflight-required` | **FIXED in source.** `GuiRetainedRenderSession.seed` now calls `engine2d_draw_ir_adv_composition_owner_with_images` (`gui_content_renderer.spl:53-56`) instead of the tiled damage wrapper. Note: subsequent non-idle `render_damage` calls (`:79-80`) still route through `engine2d_draw_ir_render_composition_damaged` without parent-sampling scratch replay if a non-idle plan hits a parent-sampling root. | `src/lib/gc_async_mut/ui/gui_content_renderer.spl:41-82` |
| 6 | `doc/08_tracking/bug/db/wm_quality_contract_glass_dark_contrast_reads_dead_palette_2026-11-26.sdn` | `glass_dark` aliased to `aetheric_dark` + contrast report reads first `--ui-bg` | **PARTIALLY FIXED (package fixed; first-declaration parser open).** `glass_dark` alias was removed and `config/themes/glass_dark/` registered. Per `.md` lines 94-96, `wm_theme_quality_report` still reads the *first* `--ui-bg` declaration instead of the effective cascade winner (affecting `aetheric_dark` / `--ui-accent`). | `doc/08_tracking/bug/wm_quality_contract_glass_dark_contrast_reads_dead_palette_2026-11-26.md:35-96` |
| 7 | `doc/08_tracking/bug/db/wm_full_stack_demo_child_frames_hardcode_default_theme_2026-11-27.sdn` | `wm_full_stack_demo` child frames hardcode `default_theme_id()` | **FIXED in demo/spec; admission gate & pre-existing compositor failures noted.** `examples/06_io/ui/wm_full_stack_demo.spl:216-240` now passes `_resolved_child_theme_id()`. `set_external_child_frame` still lacks an active-theme admission guard like top-level `set_external_content_frame`, and log #1 recorded 3 pre-existing `HostCompositor` pointer/minimize failures in `wm_full_stack_demo_spec.spl`. | `examples/06_io/ui/wm_full_stack_demo.spl:216-240`, `doc/08_tracking/bug/db/wm_full_stack_demo_child_frames_hardcode_default_theme_2026-11-27.sdn:10-11` |
| 8 | `doc/08_tracking/bug/db/wm_local_lane_clock_tick_full_repaint_2026-11-26.sdn` | Local WM lane repaints full frame on every clock tick | **FIX IMPLEMENTED / REVIEWED (2 perf caveats open).** `retained_scene_damage_plan` (`engine2d_wm_frame_executor.spl:864-934`) uses `taskbar_key`, `clock_rect`, window bounds, and content-resolved window IDs. Open caveats: clock ticks overlapping a window on Vulkan still cost ~a full frame due to full-layer readback, and `host-gpu` presents invalidate local retained state via `record_host_lane_present()` (`:939-941`). | `src/os/compositor/engine2d_wm_frame_executor.spl:864-942,1093-1130` |
| 9 | `doc/08_tracking/bug/db/wm_retained_damage_rejects_parent_sampling_window_material_2026-11-26.sdn` | Retained damage replay rejects `fluid_light`/`aetheric_dark` parent-sampling windows | **FIX IMPLEMENTED (waiting GPU/macOS verification).** `_wm_replay_parent_sampling_composition` (`engine2d_wm_frame_executor.spl:335-470`) expands damage rects by causal blur padding (`4..32`), paints non-parent backdrop to an offscreen scratch `Engine2D`, replays intersecting parent-sampling batches, and commits unpadded rects. CPU interpreter specs passed (4/4), waiting for real GPU hardware verification (`SIMPLE_2D_REQUIRE_VULKAN=1` / macOS Metal). | `src/os/compositor/engine2d_wm_frame_executor.spl:335-470,1098-1129` |
| 10 | `doc/08_tracking/bug/db/wm_content_damage_plan_api_specified_but_never_landed_2026-11-26.sdn` | `WmContentFrame` damage-plan API missing (`0/7`) | **FIXED.** `WM_CONTENT_DAMAGE_NONE`/`LOCAL`/`FULL`, `producer_revision`, `damage_mode`, `damage_resources_accepted`, and `wm_content_frame_damage_plan_valid` are implemented in `src/lib/common/ui/window_scene.spl:350-420,1254`. | `src/lib/common/ui/window_scene.spl:350-420,1254` |
