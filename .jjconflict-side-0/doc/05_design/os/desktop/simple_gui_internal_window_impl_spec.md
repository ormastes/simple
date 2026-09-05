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

### Motion provider — as-built (fix-round, 2026-07-07)

The `MotionBackgroundSource` host implementation
(`src/os/compositor/background_motion_provider.spl`, `HostMotionBackgroundSource`)
and the present-loop seam (`src/os/hosted/hosted_entry.spl`) landed as follows;
this subsection documents exactly what exists, not an aspiration.

- **Manifest source format.** A "motion" background is a plain-text manifest:
  line 1 = `frame_interval_micros` (positive integer), each remaining
  non-blank line = an ordered PPM frame path. No video codec — frames are
  plain images reused through the `kind:"image"` provider's content-hash
  cache + fit resampling (`HostBackgroundImageProvider`).
- **Frame selection is a pure function of absolute time**, not an
  incrementing counter: `raw_index = t_micros / frame_interval_micros`,
  `frame = frames[raw_index % frame_count]`. A caller that falls behind by
  several intervals lands on the frame current for that timestamp and drops
  the intervening frames rather than stalling to catch up (frame-drop, not
  backlog-replay).
- **Dirty-trigger contract.** `shared_wm_motion_background_next_due_micros()`
  exposes the absolute wall-clock micros at which the next frame becomes due
  (`-1` when no source is registered or none has been established yet — see
  sentinel below). `shared_wm_motion_dirty_due(now_micros, due_micros,
  last_fired_due_micros)` is a pure predicate that fires exactly once per due
  timestamp (`due != last_fired_due and now >= due`), keeping the present
  loop dirty-gated (GUI-5a) instead of perpetually dirty.
- **Self-re-arming seam.** The once-per-due-value contract requires next-due
  to advance to a NEW value after the trigger fires; that normally happens as
  a side effect of `frame_for_time` being called during render. No production
  render lane in the hosted chrome path (`host_compositor_entry.render_frame`)
  resolves scene backgrounds at all (it direct-draws chrome — see I8 below),
  so relying on render-side consumption alone would leave the trigger firing
  once and then going permanently stale. `shared_wm_motion_background_consume_due(t_micros)`
  (`window_scene.spl`) lets the seam itself call `frame_for_time` right after
  the trigger fires, so `hosted_entry.spl`'s loop re-arms the cadence every
  interval independent of what any render lane does.
- **Not-yet-scheduled sentinel.** `_motion_next_due_micros` (module-level
  `var`, see below) starts at `-1` ("not yet scheduled"), the same value the
  seam already uses for "no source registered". Before this fix it started at
  `0`, which the seam read as "due at the epoch" — always `<=` any real
  wall-clock `now`, causing a spurious dirty fire on the very first iteration
  after registration, before any frame had ever actually been selected. `-1`
  fails the seam's `due_micros >= 0` gate, so the trigger stays quiet until a
  real due timestamp exists. `host_compositor_entry.ensure_host_motion_background_source_registered`
  seeds the real first due once, at registration time, by calling
  `frame_for_time(rt_time_now_unix_micros())` before registering the source.
- **Single-frame degrade.** A manifest with exactly one frame is accepted
  (not an error) and behaves as a static image: `frame_for_time` always
  returns that frame and sets next-due to the sentinel horizon
  `9223372036854775807` (`_MOTION_NEVER_DUE_MICROS`), so the dirty trigger
  can never fire again for it.
- **Loud-fail matrix (construction, `HostMotionBackgroundSource.create`):**
  missing/unreadable manifest, empty manifest (no `frame_interval_micros`
  line), non-positive/non-numeric interval, and zero frame paths are all
  typed `Err`, never a silent default. At resolve time, a frame that cannot
  be decoded (deleted mid-run, corrupt) returns the sentinel
  `BackgroundSurface(width: 0, height: 0, pixels: [])`, which
  `shared_wm_scene_resolve_background` maps to the same loud `0xFFFF00FF`
  marker used for an unknown kind — **motion has no stale-serve**: I6's
  "serve last-good on transient error" behavior is a `kind:"image"`-provider
  property only; a bad motion frame is always loud, never a silently-served
  stale frame.
- **Cache reuse.** Each frame is resolved through the same fs-backed
  `HostBackgroundImageProvider` instance kind:"image" uses, so the cache key
  is the same `(content_hash(source_bytes), target_w, target_h, fit)` (I5) —
  a short loop's repeated frames are real cache hits, not re-decodes.
- **Module-level state rationale.** `next_frame_due_micros()` cannot be
  derived from `self` fields alone (unlike `frame_for_time`, which reads only
  immutable construction-time fields): a value produced by `frame_for_time`
  must be remembered *across* the call for the next `next_frame_due_micros()`
  read. Per the trait-slot re-boxing bug
  (`interp_trait_slot_receiver_reboxed_per_call_mutation_loss_2026-07-07.md`),
  `me` methods reached through the `MotionBackgroundSource?`-typed module
  slot get a freshly re-boxed receiver on every call, so a `self.field = ...`
  write inside `frame_for_time` would not be visible from the next call. The
  "next due" bookkeeping therefore lives in a bare module `var`
  (`_motion_next_due_micros`), the same workaround `background_image_provider.spl`
  already uses.
- **Env wiring.** `host_compositor_entry.ensure_host_motion_background_source_registered`
  registers a motion source once per process, gated on `SIMPLE_WM_MOTION_MANIFEST`
  (manifest path; unset keeps the no-motion lane byte-identical) and an
  optional `SIMPLE_WM_MOTION_FIT` (default `"cover"`).

### Invariant table

| # | Invariant | Enforced by |
|---|---|---|
| I1 | `kind:"color"` behavior is byte-identical to today | `shared_wm_scene_resolve_background:72-73` branch unchanged |
| I2 | Unknown/unimplemented `kind` returns the loud `0xFFFF00FF` marker, never a silent fill | `:76` marker path (`WM_BACKGROUND_UNRESOLVED_MARKER_COLOR:69`) |
| I3 | Executor stays stateless (takes `scene`, returns stats); all caching lives on the compositor, not `common.ui` | executor `:443` signature; cache in `src/os/compositor/**` |
| I4 | No per-pixel FFI to draw a background; scale via `backend.blit_pixels` / `Engine2D.draw_image` | `display_backend.spl:17`, `compositor_engine2d.spl:100` |
| I5 | Cache key = `(content_hash(source_bytes), target_w, target_h, fit)` | mirrors `WebRenderPixelArtifactCache` (`web_render_pixel_backend.spl:111`) |
| I6 | Stale-serve returns last-good surface + `stale:true` + diagnostic; loud marker only when there is NO prior good surface | provider + resolution `stale` field (`kind:"image"` only — motion has no stale-serve, see above) |
| I7 | Background must not mask chrome/title-glyph evidence | `check-simpleos-wm-visible-display-evidence.shs` still asserts glyphs on top |
| I8 | Motion source advances by wall-clock; background-only advance does NOT re-raster windows/chrome | **LANDED (2026-07-07 follow-up).** `hosted_entry.spl`'s loop tracks `other_dirty` (input/warmup) separately from `motion_dirty` (the due-motion trigger); a motion-only tick calls `HostCompositor.render_background_only(t_micros)`, which touches only `host_background_visible_rects(windows, w, h)` (desktop rect minus every visible window rect, via axis-aligned rectangle subtraction) instead of the whole frame, falling back to a full `render_frame()` only when that region can't be cheaply computed (rect-count safety cap). `host_compositor_entry.spl`'s `render_frame()` direct-draw lane also now resolves `self.background` (color/image/motion) via `_resolve_background` instead of hardcoding `theme.compositor_bg`. Specced in `wm_background_motion_hosted_consumption_spec.spl`: two absolute-time samples resolve different frames; a window-body pixel is untouched across two background-only advances. |

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
