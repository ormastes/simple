# Simple GUI Completion — Architecture (`release/1.0.0`)

- **Date:** 2026-11-28
- **Status:** Design Complete (Approved Option B + NFR Option 1)
- **Target Branch:** `release/1.0.0`
- **Requirements:** `doc/02_requirements/feature/simple_gui_completion.md`, `doc/02_requirements/nfr/simple_gui_completion.md`
- **Research:** `doc/01_research/local/simple_gui_completion_2026_11.md`, `doc/01_research/domain/simple_gui_completion_2026_11.md`

---

## 1. Architectural Principles (MDSOC+ & Additive Contracts)

1. **Additive `ScreenHost` vs `RenderBackend` Boundary (`REQ-SGUI-001`, `NFR-SGUI-005`):**
   - `common.ui.backend.RenderBackend` (`src/lib/common/ui/backend.spl`) remains the `UIState` + `render_html` trait for all 8 existing importers (`ui.tauri`, `ui.tui`, `ui.electron`, `ui.web`, `ui.vscode`, `ui.none`, `os.compositor.browser_backend`, `os.compositor.fb_backend`). Zero breaking renames or signature changes.
   - `common.ui.screen_host.ScreenHost` (`src/lib/common/ui/screen_host.spl`) remains the separate, additive DrawIR v3 seam (`host_name`, `size`, `present_scene(DrawIrV3Scene)`, `poll_input() -> HostInputEvent?`, `shutdown`).
   - Application-level backend construction lives in `app.ui.backend_factory` (`src/app/ui/backend_factory.spl`) and headless lifecycle in `app.ui.none.app.HeadlessApp` (`src/app/ui.none/app.spl`) + `nogc_sync_mut.ui.session.UISession` (`src/lib/nogc_sync_mut/ui/session.spl`). Broken unit/system specs that imported nonexistent `common.ui.backend_factory` / `common.ui.app` are updated to target these canonical modules without inventing duplicate factories in `common.ui`.

2. **Shared Event -> Layout -> `DrawIrV3Scene` / `DrawIrComposition` Pipeline:**
   ```
   Host Window (libspl_winit / GuiRenderer)
     │  physical inner_size(), scale_factor_milli(), GUI_EVT_SCALE_CHANGED,
     │  GUI_EVT_KEYBOARD + shifted + GUI_EVT_TEXT_INPUT
     ▼
   ScreenHost (ScreenGuiHost / Screen2dHost / Screen2dEngineHost / HostCompositor)
     │  logical HostInputEvent (Pointer, Key{code, ch, mods}, Resize)
     ▼
   common.ui.event / widget_hit / UISession
     │  focusable/enabled/visible tab traversal, blur, pointer capture, IME
     ▼
   common.ui.layout + widget_draw_ir + draw_ir_device_scale
     │  DrawIrComposition -> DrawIrV3Scene (or Engine2D DrawIR)
     ▼
   Rasterizer / Compositor (RasterSurface / Engine2dWmFrameExecutor / GuiRetainedRenderSession)
     │  local damage replay + causal-blur padded scratch for parent-sampling glass
     ▼
   Device Surface / Window (libspl_winit staging blit / Metal / Software readback)
   ```

3. **Process-Global Store Isolation & TinyGUI Mutation Safety (`REQ-SGUI-002`, `NFR-SGUI-002`):**
   - `WidgetNode` is a handle over `common.ui.widget_store_ops`; shared specs must isolate widget IDs by prefix.
   - `TinyGuiState` (`src/lib/nogc_sync_mut/tiny/gui/state.spl`) retains its O(1) cached child metadata fast-path during valid read sequences while detecting any direct in-place mutation to `nodes[i].bounds` or `nodes[i].parent` (fingerprinting structural layout fields when entering/validating cache).

4. **Theme Authority & Child Frame Admission (`REQ-SGUI-003`):**
   - `wm_theme_quality_report` (`src/app/ui.web/wm_quality_contract.spl`) reads the **cascade-winning** (last) CSS custom property declaration in `:root` (skipping conditional `@media` / `[data-wm-contrast=...]` blocks) rather than the first declaration.
   - `HostCompositor.set_external_child_frame` (`src/os/compositor/host_compositor_core.spl`) enforces the same active-theme identity admission policy (`_host_active_content_theme_id()`) already enforced by top-level `_set_external_web_frame_with_ownership`.

5. **Retained Damage with Causal Backdrop Expansion (`REQ-SGUI-007`, `NFR-SGUI-001`):**
   - Both `Engine2dWmFrameExecutor` and `GuiRetainedRenderSession` handle parent-sampling glass surfaces via two-phase padded replay (non-parent backdrop over causal-blur-expanded rect into scratch surface -> intersecting parent-sampling batches -> unpadded damage rect commit) rather than rejecting non-idle glass damage plans.

---

## 2. Module Ownership & Slice Architecture

| Slice | Architectural Layer | Owning Modules | Key Contract Change |
|---|---|---|---|
| **Slice 1** | Spec & Core Integrity | `test/01_unit/app/ui/*`, `test/03_system/gui/*`, `src/lib/nogc_sync_mut/tiny/gui/state.spl`, `src/app/ui.web/wm_quality_contract.spl`, `src/os/compositor/host_compositor_core.spl` | Repair 4 broken specs; TinyGUI fingerprint check; cascade-winning CSS var lookup; child-frame theme admission gate. |
| **Slice 2** | Input, Focus, HiDPI & WM Pointer | `src/lib/common/ui/event.spl`, `src/lib/common/ui/widget_hit.spl`, `src/lib/nogc_sync_mut/ui/gui_renderer.spl`, `src/app/ui_showcase/hosts/host_gui.spl`, `test/03_system/wm/wm_full_stack_demo_spec.spl` | Focusable/visible/enabled filtering; blur reset; pointer capture on pressed controls; `GuiRenderer` shift/text + `SCALE_CHANGED` plumbing; WM demo spec geometry alignment. |
| **Slice 3** | Retained Damage & Release Gates | `src/lib/gc_async_mut/ui/gui_content_renderer.spl`, `src/os/compositor/engine2d_wm_frame_executor.spl`, `test/01_unit/lib/gc_async_mut/ui/gui_content_renderer_spec.spl`, `test/03_system/gui/*` | Parent-sampling retained replay in `GuiRetainedRenderSession.render_damage`; macOS live-window & `DrawIrV3Scene` SSpec verification gates + `doc/06_spec/` manuals. |

---

## 3. Dependency & Boundary Guards

- **No `common.ui` -> `app.ui` or `os.*` reverse dependencies:** `common.ui` remains host- and OS-independent (`backend.spl`, `screen_host.spl`, `event.spl`, `widget_hit.spl`, `layout.spl`).
- **SFFI Isolation:** `GuiRenderer` (`src/lib/nogc_sync_mut/ui/gui_renderer.spl`) remains the sole dlopen boundary for `libspl_winit`; `ScreenGuiHost` consumes only `GuiRenderer` methods and never declares raw `rt_winit_*` externs.
- **Direct Env/Runtime Guard:** New or modified files under `src/app/` and `src/lib/gc_async_mut/` use `std.io_runtime` / `app.io.*` facades rather than raw `rt_env_get` / `rt_process_run`.
