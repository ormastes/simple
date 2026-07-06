# Simple GUI Internal Window Implementation Spec

Status: bridge implemented (2026-07-06); chrome/content/taskbar drawing moved
into a common.ui CompositorBackend executor, plus chrome-kind (titled /
borderless) and background-provider support (2026-07-07). A fuller Draw IR
executor can replace the current framebuffer executor later without changing
the Simple GUI scene contract.

## Goal

The WM must use the Simple GUI core for internal windows. Host WM and SimpleOS
WM must differ only in backend/config glue; they must not keep separate dummy
or evidence-only window renderers.

## Implemented Bridge

- `src/lib/common/ui/window_scene.spl` now exposes:
  - `simple_gui_internal_window(...)`
  - `simple_gui_internal_window_scene(...)`
  - `simple_gui_internal_window_renderer_handoff_marker()`
- `src/os/compositor/shared_mdi_framebuffer_scene.spl` now converts MDI seed and
  lifecycle windows through `SharedWmScene` before rendering framebuffer pixels.
- SimpleOS/QEMU framebuffer rendering consumes `SharedWmScene` through
  `render_shared_mdi_framebuffer_scene_for_simple_gui_scene(...)`.
- Host WM fallback chrome/taskbar rendering projects hosted windows into
  `SharedWmScene` with `shared_mdi_scene_from_render_windows(...)` and renders
  scene-derived window chrome/taskbar while preserving host-only content
  scroll/cache state.
- The live host WM taskbar demo opens through the `GuiRenderer` facade and the
  `spl_winit` SFFI library. App code must not import raw
  `std.io.window_winit` or call raw `rt_winit_*` externs for this lane.

## Follow-up Implementation (2026-07-07 update)

1. **Done.** Chrome/content/taskbar drawing moved out of
   `shared_mdi_framebuffer_scene.spl` into a `common.ui` executor:
   `common.ui.window_scene_draw_ir.shared_wm_scene_render_to_backend(backend,
   scene)` renders a `SharedWmScene` directly against any
   `os.compositor.display_backend.CompositorBackend` draw target (desktop
   chrome, per-window chrome/content, taskbar). `shared_mdi_framebuffer_scene.spl`
   is now glue: it builds the `SharedWmScene` (as before) and calls the
   executor; the legacy `SharedMdiRenderWindow`-shaped entrypoints
   (`render_shared_mdi_desktop_chrome`, `draw_shared_mdi_window_chrome`,
   `draw_shared_mdi_taskbar`, `render_shared_mdi_app_content`,
   `render_shared_mdi_windows_to_backend`) still exist and delegate to the
   executor, unchanged for existing callers (e.g.
   `os.compositor.host_compositor_entry.spl`). Taskbar item geometry
   (`wm_taskbar_item_width`/`wm_taskbar_dock_width`/`wm_taskbar_item_x`) moved
   from `os.compositor.wm_action_applier` into `common.ui.window_scene_draw_ir`
   (pure math, no os dependency needed by the executor); `wm_action_applier`
   re-exports the same names so its callers are unaffected.
2. **Done.** The x86_64 QEMU entry (`gui_entry_engine2d.spl`) and the host WM
   capture-evidence path both call the same
   `render_shared_mdi_framebuffer_scene*` functions in
   `shared_mdi_framebuffer_scene.spl`, which now both route through the one
   `shared_wm_scene_render_to_backend` executor. No changes were needed in
   either lane entry file — the signature-compatible glue refactor made both
   lanes share the executor automatically.
3. Preserve current readable-text evidence. Do not replace it with a fake,
   smaller framebuffer, dummy window labels, or reduced-resolution shortcut.
   (Still true; unchanged by this update — see
   `check-simpleos-wm-visible-display-evidence.shs`.)

## Chrome-Kind and Background Extension Contract (2026-07-07)

- `SharedWmWindow.chrome_kind` (`common.ui.window_scene`) is `"titled"`
  (default, standard title bar + border) or `"borderless"` (pure content
  surface for taskbar-like windows and plain drawn objects — no titlebar
  chrome pixels; z-order/focus/hit-test bounds are unchanged). Every
  `SharedWmWindow` construction site sets it explicitly or gets it via
  `simple_gui_internal_window(...)`'s default, so existing callers/bridges are
  unaffected. The executor gates the title bar/border draw call on this field
  only; content-area geometry also widens to the full window bounds for
  borderless windows (no chrome inset).
- `SharedWmScene.background: BackgroundSpec` (`kind`, `color`, `source`) is a
  provider contract, not a hardcoded fill. `kind: "color"` is implemented;
  `"image"` and `"motion"` are reserved names for later providers.
  `shared_wm_scene_resolve_background(...)` is the single resolution point:
  unknown/unimplemented kinds never silently fall back to a default fill —
  they log a diagnostic and return `resolved: false` plus the loud
  `WM_BACKGROUND_UNRESOLVED_MARKER_COLOR` (`0xFFFF00FF`) so a caller/executor
  visibly shows the failure instead of masking it. Callers that only need a
  solid color today (`shared_wm_background_color(color)`) do not need to
  change when image/motion providers land later — only
  `shared_wm_scene_resolve_background` gains a new `if` branch.

## Phase-2 Provider Design (image / motion) — 2026-07-07

Companion plan: `doc/03_plan/os/desktop/wm_window_render_api_hardening_plan.md`.
This section extends the existing loud-fail contract to the two reserved
background providers and to the borderless-window content path, without changing
the `kind:"color"` semantics that already ship.

### Executor extension points (verified anchors)

- Background resolution is the single point `shared_wm_scene_resolve_background`
  (`src/lib/common/ui/window_scene.spl:71`). It currently reads only `.kind`/`.color`
  and returns `SharedWmBackgroundResolution` (`:60`) with `resolved`, `color: u32`
  (`:62`), `error_message`. Providers extend this function with new `if` branches
  only — callers using `shared_wm_background_color` (`:57`) are unaffected.
- The executor draws the resolved background before chrome inside
  `shared_wm_scene_render_to_backend` (`window_scene_draw_ir.spl:445-446`); a
  decoded provider surface is blitted here.
- Borderless content already routes through `_shared_wm_scene_window_content_rect`
  (`window_scene_draw_ir.spl:431-433`, full-window rect for borderless) and
  `shared_wm_scene_render_app_content` (`:385`).

### Provider signatures (Simple)

```simple
# window_scene.spl — extend BackgroundSpec + resolution
struct BackgroundSpec:
    kind: text          # "color" | "image" | "motion"
    color: u32
    source: text        # image/motion content reference (was already declared, :51)
    fit: text           # NEW: "cover" | "contain" | "stretch" | "tile" (default "cover")

struct SharedWmBackgroundResolution:
    resolved: bool
    color: u32
    surface: BackgroundSurface?   # NEW: decoded RGBA + intrinsic w/h; nil for color
    stale: bool                   # NEW: true when serving last-good after a resolve error
    error_message: text

trait BackgroundImageProvider:
    fn resolve(self, source: text, target_w: i32, target_h: i32, fit: text) -> BackgroundResolveOutcome

trait MotionBackgroundSource:
    fn frame_for_time(self, t_micros: i64) -> BackgroundSurface
    fn next_frame_due_micros(self) -> i64
```

The `common.ui` executor never decodes and never touches the filesystem: a
provider is injected (host provides an fs-backed one; SimpleOS provides an
in-image pre-decoded one). This preserves the baremetal-lane boundary already
documented in `shared_wm_renderer_unification.md` (no `rt_file_exists`/theme
reads on the freestanding path).

### Invariant table

| # | Invariant | Enforced by |
|---|---|---|
| I1 | `kind:"color"` behavior is byte-identical to today | `shared_wm_scene_resolve_background:72-73` branch unchanged |
| I2 | Unknown/unimplemented `kind` returns the loud `0xFFFF00FF` marker, never a silent fill | `:76` marker path (`WM_BACKGROUND_UNRESOLVED_MARKER_COLOR:69`) |
| I3 | Executor stays stateless (takes `scene`, returns stats); all caching lives on the compositor, not `common.ui` | executor `:443` signature; cache in `src/os/compositor/**` |
| I4 | No per-pixel FFI to draw a background; scale via `backend.blit_pixels` / `Engine2D.draw_image` | `display_backend.spl:17`, `compositor_engine2d.spl:100` |
| I5 | Cache key = `(content_hash(source_bytes), target_w, target_h, fit)` | mirrors `WebRenderPixelArtifactCache` (`web_render_pixel_backend.spl:111`) |
| I6 | Stale-serve returns last-good surface + `stale:true` + diagnostic; loud marker only when there is NO prior good surface | provider + resolution `stale` field |
| I7 | Background must not mask chrome/title-glyph evidence | `check-simpleos-wm-visible-display-evidence.shs` still asserts glyphs on top |
| I8 | Motion source advances by wall-clock; background-only advance does NOT re-raster windows/chrome | present-loop cadence gate (dirty region = background only) |

### Error semantics (extends the loud-fail contract)

- **No provider injected but `kind:"image"`/`"motion"`** → loud `0xFFFF00FF` marker
  (`resolved:false`), same as an unknown kind. Providers are additive; absence is
  a visible failure, not a silent fallback.
- **Resolve/decode hard-fail, no prior good surface** → loud marker + `error_message`.
- **Resolve/decode fail after a prior success** → serve last-good surface,
  `resolved:true`, `stale:true`, emit diagnostic (no wallpaper flash on a transient
  read error, but the staleness is observable).
- **Motion source over budget** → drop frames (source-side), never stall the input
  path; the present loop keeps its dirty-gated cadence (GUI-5a) intact.

### Lane-parity requirements

- Host and SimpleOS differ only in the injected provider (fs-backed vs in-image)
  and backend config — not in scene shape, resolution branch, or invariants
  (the source-ownership boundary of `shared_wm_renderer_unification.md`).
- SimpleOS end-to-end visual proof of image/motion is **blocked** by the
  freestanding module-init/primitive-global fault
  (`doc/08_tracking/bug/freestanding_wrapper_profile_i32_global_var_shifted_2026-07-02.md`,
  P2 OPEN; memory `project_simpleos_gui_boot_2026-05-28.md`). Until it lands, the
  host lane is the visual-proof vehicle; the SimpleOS lane keeps its worked-around
  chrome/text evidence. See plan item D.

## Verification

Run after implementation:

```sh
bin/simple check src/lib/common/ui/window_scene.spl
bin/simple check src/os/compositor/shared_mdi_framebuffer_scene.spl
bin/simple check src/lib/nogc_sync_mut/ui/gui_renderer.spl
bin/simple check src/os/compositor/hosted_backend_gui_renderer.spl
bin/simple check src/os/compositor/host_compositor_entry.spl
SIMPLE_BIN=bin/simple BUILD_DIR=build/wm_multiapp_taskbar_gui_renderer WM_MULTIAPP_TIMEOUT_SECS=180 sh scripts/check/check-wm-multiapp-taskbar-evidence.shs
SIMPLE_BIN=bin/simple BUILD_DIR=build/hosted_wm_capture_simple_gui_shared sh scripts/check/check-hosted-wm-capture-evidence.shs
SIMPLE_BIN=bin/simple BUILD_DIR=build/simpleos_wm_visible_display_simple_gui_shared SIMPLEOS_WM_VISIBLE_MARKER_TIMEOUT_SECS=120 sh scripts/check/check-simpleos-wm-visible-display-evidence.shs
SIMPLE_BIN=bin/simple BUILD_DIR=build/simpleos_wm_qmp_drag_delta_simple_gui_shared SIMPLEOS_WM_QMP_LAUNCH_TIMEOUT_MS=120000 sh scripts/check/check-simpleos-wm-qmp-drag-delta-evidence.shs
```

The QEMU visible-display gate should continue to validate readable title glyphs,
not only nonblack/color/taskbar pixels.
The host multi-app taskbar gate should continue to validate app launch,
taskbar focus/minimize/restore, readable title text, close-button pixels, and
captured real-window frames through the self-hosted Simple binary plus
`SIMPLE_SPL_WINIT_PATH`, not a Rust seed GUI driver.
