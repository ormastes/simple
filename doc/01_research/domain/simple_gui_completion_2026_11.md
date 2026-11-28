# Simple GUI Completion — Domain Research (2026-11)

- **Date:** 2026-11-28
- **Method:** External domain synthesis via `search_web` mapped onto Simple's `common.ui`, `ui_showcase`, and `os.compositor` architecture.

---

## 1. Retained-Mode UI Damage Invalidation with Backdrop-Sampling Expansion

### External Industry Consensus (Chromium Viz / Skia / Wayland Compositors)
1. **Bounding-Box Damage Mismatch on Backdrop Filters:** In retained-mode compositors, `backdrop-filter: blur(R)` (frosted glass / vibrancy panels) samples pixels *underneath and outside* the local damage rectangle up to the kernel's support footprint (typically `~3 * R` for Gaussian approximations or bounded box-blur radius `R`).
2. **Failure Modes Without Causal Expansion:**
   - **Edge bleeding / uninitialized borders:** If only the unpadded damage rect is rasterized into a scratch/offscreen target, the blur kernel reads stale foreground pixels or zeros outside the clip edge.
   - **Under-invalidation across overlapping layers:** When an animation (such as a clock tick or cursor blink) updates behind or adjacent to a translucent surface, standard rect damage fails to re-evaluate the backdrop-filtered surface unless the dependency graph expands damage by the filter's causal radius.
3. **Standard Mitigation Pattern:**
   - **Two-phase padded replay:** Expand damage rects by `causal_pad` (clamped to viewport bounds), replay non-sampling backdrop layers over the **padded** rect into an offscreen surface, evaluate intersecting backdrop-sampling layers over that clean backdrop, and commit **only the unpadded** damage rects back to the retained framebuffer.
   - **Dependent layer invalidation:** Changes to backdrop content intersecting a glass surface's expanded footprint invalidate that glass pass, while disjoint non-intersecting glass surfaces are culled completely.

### Mapping to Simple GUI
- `Engine2dWmFrameExecutor._wm_replay_parent_sampling_composition` (`src/os/compositor/engine2d_wm_frame_executor.spl:335-470`) implements this exact two-phase padded offscreen replay (`causal_pad` clamped to `4..32`, `padded_rects = _wm_expand_and_coalesce_rects(...)`, unpadded commit back to `self.engine`).
- **Remaining gap:** `GuiRetainedRenderSession.render_damage` (`src/lib/gc_async_mut/ui/gui_content_renderer.spl:66-82`) still dispatches directly to `engine2d_draw_ir_render_composition_damaged` without a parent-sampling scratch replay when a non-idle `DamagePlan` hits a glass root surface; and on Vulkan, window-overlapping clock ticks still pay full-layer readback cost.

---

## 2. HiDPI Logical-to-Physical Layout & Font Scaling on macOS Cocoa / winit

### External Industry Consensus (AppKit `NSWindow` + `winit`)
1. **Coordinate Space Separation:**
   - **Logical coordinates (points):** Used for window intent, layout bounds, hit-testing, and pointer coordinates so UI ergonomics stay constant across 1x and 2x Retina displays.
   - **Physical coordinates (backing pixels):** `PhysicalSize = LogicalSize * backingScaleFactor` (`window.inner_size()`). Framebuffers, pixel staging buffers, and swapchains must match exact physical dimensions (`inner_size()`) rather than relying on OS bitmap upscaling or nearest-neighbor downsampling (which breaks 1px glyph strokes).
2. **Typography at Device Scale:**
   - Font sizes are specified in logical points and multiplied by `scale_factor` prior to rasterization/atlas generation (e.g., `14pt` at `2.0x` rasterizes glyphs at `28px` while advancing layout in logical units).
3. **Dynamic Scale Changes (`ScaleFactorChanged`):**
   - Moving a window between a Retina MacBook Pro panel (`2.0x`) and an external 1080p/4K display (`1.0x` or fractional) emits `WindowEvent::ScaleFactorChanged`. The host must update its cached scale factor, recompute logical/physical dimensions, invalidate retained framebuffers/caches, and trigger a full redraw.

### Mapping to Simple GUI
- **Already aligned:** `draw_ir_composition_at_device_scale` (`src/lib/common/ui/draw_ir_device_scale.spl:454-466`) preserves logical layout and scales `DrawIrComposition` geometry + `font-size-milli` + `device-advance-widths` + `device-glyph-xs` for Engine2D. `ScreenGuiHost.open` (`src/app/ui_showcase/hosts/host_gui.spl:178-190`) reads `gui.inner_size()` and `gui.scale_factor_milli()`.
- **Remaining gaps:**
  1. `ScreenGuiHost.poll_input` (`src/app/ui_showcase/hosts/host_gui.spl:218-255`) and `gui_event_to_host` (`:110-146`) drop `GUI_EVT_SCALE_CHANGED` (`src/lib/nogc_sync_mut/ui/gui_renderer.spl:74`), so dynamic multi-monitor DPI changes are ignored.
  2. `gui_device_scale` (`host_gui.spl:40-54`) rounds fractional scales (`1.25`, `1.5`) to integers, and `GUI_EVT_RESIZED` recomputes `dev_w = resize_w * self.scale`, risking 1px mismatch when physical `inner_size` is not an exact multiple of `scale`.
  3. `ScreenGuiHost` uses `RasterSurface` integer-scaled 5x7 bitmap glyphs (`scene_raster.spl`) instead of vector/SFNT glyphs scaled via `draw_ir_device_scale.spl` + `Engine2D`.

---

## 3. Widget Tree Hit-Testing, Focus Traversal, and Input Lifecycle Patterns

### External Industry Consensus (Flutter / Web DOM / Qt)
1. **Z-Order & Pointer Policy Hit-Testing:**
   - Hit-testing walks the laid-out tree in **reverse paint order** (topmost overlay/popup/floating window first) and respects visibility, enabled state, and pointer-transparency (`pointer-events: none` / `IgnorePointer`).
2. **Pointer Capture:**
   - A `pointerdown` that initiates a press, drag, or scrollbar scrub acquires **pointer capture** so subsequent `pointermove` and `pointerup` events route exclusively to the capturing widget (even outside its bounds) and activate/click only if released appropriately (or cancel cleanly on focus loss).
3. **Focus Tree vs Visual Tree & Tab Traversal:**
   - Sequential keyboard navigation (`Tab` / `Shift+Tab` / `FocusNext` / `FocusPrev`) traverses only **focusable, enabled, visible** nodes ordered by explicit `tab_index` (with declaration order tie-breaking), optionally trapped within modal dialogs/popups.
   - Shifting focus emits explicit **blur** on the prior focus owner (canceling active preedit/hover-press states as needed) and **focus** on the new owner.
4. **Modifier & IME Lifecycle:**
   - Keyboard events carry modifier state (`Shift`, `Ctrl`, `Alt`, `Meta`) alongside canonical keycodes and printable text/IME input (`CompositionUpdate` preedit + `CompositionCommit`), rather than guessing unshifted ASCII from physical keycodes.

### Mapping to Simple GUI
- **Already aligned:** `widget_hit.spl:673-742` implements layered reverse-order hit-testing across context menus, dropdowns, floating internal windows (`z_order`), and main tree rects; `DrawIrV3HitShapeTable` (`draw_ir_v3.spl:185-200`) already has `z_indices`, `enableds`, and `pointer_policies`; `event.spl:387-398` and `widget_hit.spl:385-412` implement `CompositionUpdate` / `CompositionCommit` with Unicode char-indexed carets.
- **Remaining gaps:**
  1. `get_focusable_ordered` (`event.spl:474-515`) returns *all* non-empty widget IDs (labels, panels, disabled/hidden nodes) instead of filtering to focusable, enabled, visible controls.
  2. `handle_focus_event` (`event.spl:400-411`) is a no-op for `"blur"`, and `handle_pointer` / `widget_dispatch_pointer_up` (`event.spl:277-302`, `widget_hit.spl:775-783`) lacks unified pointer capture for non-drag controls (buttons trigger click on `down` rather than captured `up`).
  3. `GuiWindowEvent` (`gui_renderer.spl:81-89`) omits keyboard modifier bits and `GUI_EVT_TEXT_INPUT` strings, forcing `host_gui.spl:80-108` into an unshifted-only key table.
  4. `TinyGuiState.metadata_valid` (`src/lib/nogc_sync_mut/tiny/gui/state.spl:68-77`) keys cache validity solely off `nodes.len()`, risking stale layout metadata after same-length mutations.

---

## Sources Consulted (via `search_web`)
- MDN / Chromium Viz / Skia `backdrop-filter` blur-radius damage expansion and offscreen render-pass invalidation literature.
- Apple AppKit `NSWindow.backingScaleFactor` & `winit` Cocoa HiDPI documentation (`LogicalSize`, `PhysicalSize`, `ScaleFactorChanged`, font point-to-pixel scaling).
- Flutter / Web DOM / UI framework architecture references on hit-test z-order, pointer capture, `tabIndex` focus traversal, and IME composition lifecycle.
