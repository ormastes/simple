# WM GUI Window Drawing Feature Expert

## Role

Own feature-specific process knowledge for capture-based verification that the
two WM lanes actually DRAW windows, titlebars, taskbar, and correctly-sized
text: (a) the compositor scene/CSS lane (`os.compositor.wm_scene`) and (b) the
hosted-compositor chrome lane (`os.compositor.host_compositor_entry`). This is
a regression gate for the giant-text "font:" shorthand bug class (CSS weight
parsed as size), not a general WM feature area.

## Pipeline Links

- [verify skill](../../../../.claude/skills/verify/SKILL.md)

## Feature Links

- Driver (probe): [src/os/compositor/wm_gui_window_drawing_evidence.spl](../../../../src/os/compositor/wm_gui_window_drawing_evidence.spl)
  — renders 3 scenes at 1024x768, writes PPM captures, prints per-scene pixel
  metrics (non-background / text-ink "bright" / saturated "accent" counts,
  plus `max_glyph_run_px` — the giant-glyph pathology detector).
- Check script: [scripts/check/check-wm-gui-window-drawing-evidence.shs](../../../../scripts/check/check-wm-gui-window-drawing-evidence.shs)
  — runs the driver, converts each PPM to PNG (`sips`), classifies pass/fail
  per scene, writes `build/wm_gui_window_drawing/report.md`.
- Gate contract spec: [test/03_system/check/wm_gui_window_drawing_spec.spl](../../../../test/03_system/check/wm_gui_window_drawing_spec.spl)
  — pins the script/driver structural contract and the Rust-seed-forbidden
  rejection path (fast, deterministic; does not run the multi-minute render).
- Scene builders exercised: `standard_wm_scene`, `shared_wm_scene_to_chromed_wm_scene`,
  `render_scene_to_backend` in [src/os/compositor/wm_scene.spl](../../../../src/os/compositor/wm_scene.spl).
- Hosted chrome lane exercised: `HostCompositor`, `HeadlessHostCompositorBackend`,
  `render_frame`, `host_chrome_scene_html` in
  [src/os/compositor/host_compositor_entry.spl](../../../../src/os/compositor/host_compositor_entry.spl).
- Underlying CSS/GUI-web renderer (both lanes funnel through this on
  Metal-capable hosts): [src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl](../../../../src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl)
  — owned by a different, adjacent feature area; this gate is a consumer/
  regression check on it, not its owner.
- Related layer expert: [doc/00_llm_process/layer_expert/os_compositor/skill.md](../../layer_expert/os_compositor/skill.md)
- Precedent capture-evidence checks (style/idiom source): `scripts/check/check-hosted-wm-capture-evidence.shs`,
  `scripts/check/check-widget-shells-crossengine-evidence.shs`,
  `src/os/compositor/hosted_wm_capture_evidence.spl`.

## Handoff Notes (2026-07-03)

- **RESOLVED 2026-07-03 — giant-text regression re-landed and fixed**: the
  `wm_scene_css` capture at 1024x768 previously showed "Simple Web WM"
  rendered at ~400-600px/glyph (`max_glyph_run_px=425` vs the <40 floor).
  Root cause: `simple_web_html_layout_renderer.spl` parsed the `font:`
  shorthand with `parse_int(font_norm)`, so `font:600 12px system-ui` yielded
  font-size 600 (weight-as-size), which then flowed to BOTH the software
  painter (`glyph_scale(600)=75`) and the Engine2D fast-lane executor
  (`text_metrics` scale `600/7=85`). The executor / `draw_text` was NOT at
  fault — it already converts px -> cell scale. Commit `70cd415c55` claimed
  the fix but its renderer hunk was lost in a torn commit; it has now been
  RE-LANDED: helper `parse_font_shorthand_size_px` (next to `parse_int_range`,
  "first number attached to px") is called from the `font` shorthand branch
  in `compute_styles`. Probe confirms the WM-scene Draw IR TEXT font-size is
  now 12 (was 600). Resolved bug doc:
  `doc/08_tracking/bug/webengine_font_shorthand_weight_parsed_as_size_2026-07-03.md`.
  Re-run the gate to confirm `giant-glyph-pathology` flips green.
- **RESOLVED 2026-07-03 — chromed-scene interpreter crash fixed at the root**:
  `wm_scene_windows` (shared_wm_scene_to_chromed_wm_scene, 3 windows +
  taskbar) aborted with `error: semantic: cannot assign to const
  'child_styles'`. Actual root cause (NOT the `var x = if ...` form): the
  interpreter's `CONST_NAMES` set has function lifetime with no block
  scoping, so the absolute-child branch's `val child_styles` (renderer
  ~6974) const-poisoned the flex main loop's `var child_styles` (~7036) for
  the rest of the `layout()` call; the align-stretch reassignment (~7087)
  then aborted. Trigger = a flex container with BOTH a `position:absolute`
  child AND a heightless stretch child in one layout() call — which only the
  chromed scene's HTML has. Fixed in
  `src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs`
  (`bind_let_pattern_element`): a mutable binding now removes the name from
  `CONST_NAMES`. Bug doc:
  `doc/08_tracking/bug/interp_const_names_branch_val_poisons_var_2026-07-03.md`.
  The gate's per-scene process isolation (`WM_GUI_WINDOW_DRAWING_SCENE` env)
  is what localized the crash to one scene instead of erasing all captures —
  keep that design.
- **Metric design: ink (exact white) vs bright (>210)**: on a correct WM
  render the near-white glass-panel gradients alone measure ~220k "bright"
  pixels with tall vertical runs, so the glyph detector MUST key off exact
  white (255/255/255) — text in both lanes is solid `color:white` /
  `theme.text_primary` bitmap glyphs with no antialiasing, and CSS gradient
  panels never reach 255 on all channels. Do not merge the two classes back.
- **Stale self-hosted binary**: `bin/simple` (release 2026-06-05) aborts on
  `unknown extern function: rt_u32s_from_raw` before rendering — current
  renderer source needs a newer runtime extern. The check script fail-closes
  on this by default; `WM_ALLOW_SEED_DRIVER=1` + explicit `SIMPLE_BIN` is the
  documented opt-in (provenance stamped `rust-seed-opt-in` in evidence +
  report) until a fresh self-hosted binary is deployed.
- **Render cost measured**: `standard_wm_scene` 1024x768 via the engine2d
  fast lane took 243278ms (~4min) under the interpreted seed driver; render
  time >120s is REPORTED (`render_slow`), not failed — a drawing gate should
  not hard-fail on a documented perf finding.
- **GATE GREEN 2026-07-04** (all 3 scenes, gui/debug seed driver, uncontended):
  wm_scene_css 32s glyph=7, wm_scene_windows 286s glyph=13, host_compositor
  22s glyph=14 — `wm_gui_window_drawing_status=pass`. What it took, in order:
  font-shorthand fix, CONST_NAMES interpreter fix, 28x CSS-parse fix, rgba
  alpha compositing (software + Metal MSL blend_src_over, parity-pinned),
  stroke-narrow glyph discriminator, inline compositor span writes (below),
  and the driver reading `comp.backend.pixels` (a local pre-compositor
  binding does NOT see mutations made through comp.backend — it captured an
  all-zero buffer).
- **put_pixel me->me clone workaround (2026-07-04)**: HeadlessHostCompositor-
  Backend.fill_rect/blit_pixels write self.pixels inline with once-up-front
  clamping — a per-pixel `me`->`me` put_pixel call deep-clones the whole
  framebuffer per write under the interpreter (fill_rect 300x200: >120s ->
  333ms; host lane scene: >1800s timeout -> 22s). Single-shot me->me calls
  (draw_text -> fill_rect once) are fine. Interpreter root cause still open:
  doc/08_tracking/bug/interp_compositor_backend_put_pixel_clones_framebuffer_2026-07-03.md.
- **Spec fakes must implement the FULL CompositorBackend trait** (incl.
  blit_pixels) — conformance is lazily checked, so a missing method only
  aborts when the class is first instantiated. Direct-draw-path assertions
  must pin `host_wm_force_direct_chrome(true)` around render_frame: on
  Metal hosts chrome otherwise routes via the CSS fast lane (blit_pixels +
  present only) and per-element counters never fire; content marker colors
  (0xFF2050A0 title / 0xFF182230 body) must also be classified in
  blit_pixels, not only fill_rect.
- **Host lane is ~8x slower than the scene lane at the same resolution**
  (40+ min vs ~5min at 1024x768 with 3 windows): `HostCompositor.render_frame`
  does the full-frame chrome CSS render PLUS one complete CSS render per
  window content (`render_simple_web_app_content` ->
  `simple_web_app_pixel_artifact_with_theme` ->
  `compositor_render_request_artifact` = a full HTML/CSS pipeline per window
  every frame; window content is deliberately excluded from the chrome
  fingerprint cache). Budget the gate timeout accordingly (default 3600s per
  scene); a per-window-content pixel cache is the obvious perf fix if this
  lane ever needs to be interactive under the interpreter.
- **Perf gotcha (important for any future edit to this driver or to
  `wm_scene.scene_to_html`)**: `standard_wm_scene`'s `scene_to_html()` embeds
  one giant WM chrome stylesheet (tens of KB, ~47+ CSS rule blocks covering
  every WM surface — command palette, control center, notification center,
  etc.) regardless of how few scene elements are actually present. Under the
  interpreter, a single `render_scene_to_backend()` call therefore costs
  **far longer than pixel count alone would suggest** — a 64x48 (3072px)
  scene took over 3 minutes just from stylesheet parse/cascade cost. Do not
  assume "small canvas = fast render" for this scene family; budget capture
  timeouts (and CI-style gate timeouts) generously (10+ minutes per scene),
  and do not shrink capture resolution as a workaround — the cost is
  stylesheet-bound, not pixel-bound.
- **Interpreter perf gotcha in the driver's own metrics code**: an
  o(w*h) per-pixel measurement pass that calls small helper functions
  (channel-extract, min/max, brightness predicate) per pixel does NOT
  finish inside a 300s budget at 1024x768 (786432 px) — interpreted
  function-call overhead dominates. Fixed by inlining all per-pixel
  arithmetic directly in the loop body (no helper calls, no `y*width+x`
  multiply — a running flat index instead). See `_measure()` in the driver.
  Any future per-pixel analysis added to this driver must stay inlined.
- **WM theme shares the GUI (CSS) theme (2026-07-04)**: `SimpleTheme` (the
  widget CSS token source) projects onto `WmChromeColors` via
  `apply_simple_theme_to_wm_chrome(theme)` /
  `wm_chrome_colors_from_simple_theme` (common/ui/simple_theme.spl), built
  on the token-string mapper `wm_chrome_colors_from_gui_tokens`
  (common/ui/wm_chrome_theme.spl). Token map: --ui-bg→desktop/compositor
  bg, --ui-fg→text, --ui-accent→accent+focused titlebar, --app-surface→
  taskbar/command lane/window bodies, --app-surface-hover→unfocused
  titlebar, --ui-error→close button. Per-field fallback to the
  byte-identical defaults keeps this gate's pixel expectations valid until
  a theme is actually applied. Contract: wm_chrome_theme_spec "WM chrome
  shares the GUI (CSS) theme" (10/10). The spec pins the direct-rect
  fallback via `wm_scene_direct_rect_pixels` (its own entry point) because
  whether render_scene_to_backend reaches that lane is environment-dependent.
- Metric definitions (`non_bg` / `bright` / `accent` via channel-spread,
  background literal `r=15,g=23,b=42` = `0xFF0F172A` /
  `wm_chrome_theme().compositor_bg`) intentionally mirror
  `scripts/check/validate_hosted_wm_capture_ppm.spl` so this gate's raw
  counts are cross-checkable against the existing hosted-WM capture
  precedent instead of inventing new thresholds from scratch.
- `HeadlessHostCompositorBackend` (in `host_compositor_entry.spl`) is the
  reusable real pixel-capture backend for `HostCompositor` — construct it as
  a local `val`, pass it into `HostCompositor.new(backend, size)`, and read
  `backend.pixels` back after `render_frame()`; do not reuse the test-only
  `CaptureCompositorBackend` from `host_compositor_entry_spec.spl` outside
  that spec (it tracks module-global counters, not a readback pixel buffer).
- Status as of this handoff: gate authored, run end-to-end on the seed
  driver (`WM_ALLOW_SEED_DRIVER=1`), and it correctly FAILS with
  `giant-glyph-pathology` on the CSS-lane scenes while the missing renderer
  fix (above) is un-landed — an intended red. Always read
  `build/wm_gui_window_drawing/report.md` for the latest run's actual
  status/pixel counts; this gate is too slow for a fast pre-commit path.

## Multi-App Launch + Working Taskbar (live GPU capture lane)

A sibling, LIVE (on-screen winit-buffer backend) capture lane proves the Simple WM
can launch MULTIPLE GUI apps as internal windows and that the TASKBAR works
(clicking a taskbar item focuses/restores its window). Distinct from the
headless PPM lanes above — it runs a real host window and screencaptures
it.

- Demo: [examples/06_io/ui/wm_multiapp_taskbar_gui.spl](../../../../examples/06_io/ui/wm_multiapp_taskbar_gui.spl)
  — opens a 512x384 winit window, creates the common
  `HostedWinitBufferBackend`, constructs a real `HostCompositor`, launches
  Terminal/Editor/File Manager/Calculator via
  `apply_bridge_request(COMP_CREATE_WINDOW)`, renders frames through the shared
  compositor backend, and drives taskbar interactions on the REAL compositor.
- Check script: [scripts/check/check-wm-multiapp-taskbar-evidence.shs](../../../../scripts/check/check-wm-multiapp-taskbar-evidence.shs)
  (output dir `build/wm_multiapp_taskbar/` — distinct from `build/wm_gui_window_drawing/`).
- Pixel validator: [scripts/check/measure_wm_multiapp_taskbar.spl](../../../../scripts/check/measure_wm_multiapp_taskbar.spl)
  — validates the captured WM client frame, self-calibrates logical->physical
  scale from the actual capture, checks each window's titlebar band, title text,
  close button, and taskbar item, and writes per-window crops.
- Contract spec: [test/03_system/check/wm_multiapp_taskbar_spec.spl](../../../../test/03_system/check/wm_multiapp_taskbar_spec.spl)
  — exercises the pure compositor state machine (launch grows count; taskbar
  click focuses a background window; minimize + taskbar-restore) plus the gate's
  fail-closed contract.

Resolution/performance rule: never speed up this lane by shrinking the window,
lowering physical pixels, reducing DPI, dropping text, replacing widgets with
markers, or bypassing theme/rendering quality. WM targets must be engineered for
8K-class and larger desktops plus at least 300 DPI readable output. Acceptable
optimizations remove real overhead only: duplicate full-frame copies, per-pixel
FFI, avoidable allocations, missing dirty-state, or scalar hot loops.

Hard-won lessons for this live lane (each cost hours):

- **Taskbar clicks were not wired into the compositor.** `render_frame()` never
  drew a taskbar and `host_compositor_left_button_at()` never checked
  `hit_taskbar()`. Added a taskbar-hit branch at the top of the button handler:
  a press inside the dock band that lands on an item calls
  `focus_window(id)` (which also un-minimizes) — so a single taskbar click both
  focuses a background window and restores a minimized one. This is genuine
  production behavior now, not demo-only.
- **`HostCompositor` value semantics.** Class params pass by REFERENCE, so `me`
  methods called via a param (e.g. `comp.apply_bridge_request(...)` inside a
  helper) mutate the caller's object. BUT the free functions
  `host_compositor_left_button_at` / `host_compositor_minimize_focused` do
  `var out = comp` (a COPY) and return the modified copy — you MUST capture the
  return (`comp = host_compositor_left_button_at(comp, ...)`), or the mutation is
  lost. `var comp`, not `val comp`.
- **CPU per-pixel compositing is unusable under the interpreter.** Any draw
  routed through `HeadlessHostCompositorBackend.put_pixel` (which
  `fill_rect`/`draw_text`/`blit_pixels` and `app_content.render_app_content` all
  use) CLONES the whole framebuffer on EACH pixel — measured ~28ms/pixel at
  1024x768, i.e. a `fill_rect(300x200)` never finishes inside 120s. The killer is
  a `me` method calling another `me` method (`fill_rect` -> `put_pixel`): the
  second `self` borrow forces a Cow clone of the pixel array per call. An inline
  clear (single method, no sub-call) is O(n). This is why the headless
  `wm_gui_window_drawing` lane budgets 30-min timeouts. The live lane instead
  draws on the GPU via `MetalBackend.draw_rect_filled` (one FFI dispatch per
  rect), then `read_pixels_gpu_only` + pack + `winit_present_rgba`. Filed as a
  bug (see doc/08_tracking/bug/).
- **A CPU compose that blocks the winit event loop ~30s gets the app killed by
  the OS.** Keep frames fast (GPU) and pump `winit_poll_input` around readback/
  pack. The GPU lane keeps per-frame CPU work to the ~196k-pixel readback+pack.
- **Capturing the winit window on macOS is the hard part — solved with
  `screencapture -l<CGWindowID>`.** A background `open -n` app is never the
  foreground app, so its window lives on a Space that `screencapture -x` (current
  Space) never shows — every `-x` shot is the desktop wallpaper, and no
  activation (`set frontmost`, `open`, `AXRaise`, bundle-id `activate`) reliably
  switches Spaces in this automation context (all empirically produce
  wallpaper). `AXRaise`/`position of window 1` also fail — winit windows are not
  AX-enumerable. The robust primitive is `screencapture -l<windowid>`, which
  captures a window by its CoreGraphics id regardless of Space or foreground and
  needs NO activation. Get the id from `CGWindowListCopyWindowInfo` via JXA
  (`osascript -l JavaScript` + ObjC bridge). SELECT BY WINDOW TITLE: winit owns
  several process windows (a full-width menu-bar window ~1710x34pt, a blank metal
  helper ~500x500pt, and the content window), and neither max-area nor
  max-min-dimension picks the content window — match `kCGWindowName` against the
  exact `winit_window_new` title ("Simple WM — Multi-App") instead. Window names
  require Screen Recording permission (the driving Terminal already holds it).
- The WM content is located WITHIN that window capture by a **magenta locator
  frame** (0xFFFF00FF drawn at the render-buffer edges) — magenta never occurs in
  normal UI, so the validator finds its bbox and derives the logical->physical
  scale (self-calibrating, no AX/geometry dependency). Going fullscreen is NOT
  needed with `-l` capture (and winit fullscreen doesn't even engage for a
  background app — the inner size never grows).
- The demo's per-app content is drawn with distinct inline GPU rects (Terminal
  prompt lines, Editor gutter+text, File Manager sidebar+list, Calculator
  display+button grid), NOT `app_content.render_app_content` — the latter is the
  CPU per-pixel path above and is infeasible live under the interpreter.

## Handoff Notes (2026-07-06)

- **NEW — GuiRenderer facade + `spl_winit` SFFI cdylib (real interactive
  `--open` window)**: `src/app/ui.browser/app.spl` no longer declares raw
  `rt_winit_*`-style externs; its `browser_winit_*` wrapper functions
  (`browser_winit_event_loop_new`, `browser_winit_window_new`,
  `browser_winit_event_loop_poll_events`, `browser_winit_event_get_type`,
  `browser_winit_event_keyboard_input`, `browser_winit_event_mouse_moved`,
  `browser_winit_event_mouse_button`, `browser_winit_window_present_rgba`,
  `browser_winit_window_free`, `browser_winit_event_loop_free`) now delegate to
  a single `_host_gui: GuiRenderer` instance
  ([src/lib/nogc_sync_mut/ui/gui_renderer.spl](../../../../src/lib/nogc_sync_mut/ui/gui_renderer.spl)).
  `GuiRenderer` dlopens a standalone sibling cdylib built from
  [src/runtime/spl_winit/src/lib.rs](../../../../src/runtime/spl_winit/src/lib.rs)
  (winit 0.30 + softbuffer; no seed/bootstrap rebuild — see
  `feedback_no_bootstrap_rebuild.md`). Build it with
  `scripts/build/build_spl_winit.shs`, which stages
  `build/sffi/libspl_winit.<dylib|so|dll>`; the facade resolution order is
  `$SIMPLE_SPL_WINIT_PATH` override, then that staged path. Drag/click/close
  proven live on macOS with a real interactive window.
- This removed `RT:src/app/ui.browser/app.spl` from
  `scripts/check/ui_backend_isolation_baseline.txt` (app.spl now goes through
  the facade only, per `doc/04_architecture/ui/rendering/backend_isolation_architecture.md`).
  `RT:src/app/ui.browser/backend.spl` remains baselined and unaffected.
- Related bug record filed alongside this change:
  `doc/08_tracking/bug/interp_enum_match_class_name_collision_2026-07-06.md`.

## Handoff Notes (2026-07-06, GPU-offload landing)

- **Persistent Engine2D GPU sessions (task #17) + hosted-WM engine2d raster
  lane adoption (task #28-A) landed together.** `Engine2D.create_with_backend_fast`
  is the session constructor to reuse across a redraw loop (widget showcase
  `main()`, `HostCompositor`'s `Engine2dCompositorBackend`) instead of the old
  create/shutdown-per-frame pattern — for Metal this keeps the GPU
  device/queue/framebuffer alive across frames instead of re-initializing it
  every redraw (raster-bound speedup measured 176x-684x vs. per-frame
  create+shutdown, see `test/02_integration/rendering/engine2d_gpu_offload_evidence.spl`).
- **Env knobs:** `SIMPLE_GUI_BACKEND` selects the Engine2D backend key (e.g.
  `metal`/`software`/`vulkan`); `SIMPLE_WM_RASTER=engine2d` opts the live hosted
  WM lane (`src/os/hosted/hosted_entry.spl`) into the persistent
  `Engine2dCompositorBackend` instead of the default `HostedWinitBufferBackend`
  — unset/any-other-value keeps the historical default lane byte-identical;
  `SIMPLE_ONE_CALL_UPLOAD` gates the single-native-call Metal upload path
  (mirrors the existing `SIMPLE_ONE_CALL_READBACK` split — see
  `backend_metal.spl`'s `_dispatch_metal_image`).
- **Frame handoff pattern for the engine2d raster lane:** the compositor draws
  into its own Engine2D session (`comp.backend`), then
  `comp.backend.get_pixel_buffer()` is blitted into a plain winit buffer
  (`rt_winit_buffer_blit_pixels`) and presented (`rt_winit_buffer_present`) —
  the winit buffer is NOT wrapped in `CompositorBackend`, it is only a present
  sink for the already-composed frame. Provenance
  (`comp.backend.frame_provenance()`) is logged every frame and must show
  `source=device_readback` on Metal, never a silent `cpu_mirror` fallback
  presented as GPU rendering; `comp.backend.shutdown()` on every exit path.
- **`device_readback` provenance gate:** `test/03_system/gui/engine2d_gpu_offload_contract_spec.spl`
  pins both the showcase and hosted-WM adoption sites as source contracts
  (`hosted_entry.spl` is a real winit `fn main()` entry, so it's pinned by
  content-grep rather than imported+run headless), plus a content pin (not
  just length) on `HostCompositor.render_frame()`'s pixel buffer — a
  zeroed/garbage readback fails the corner+centre color check where a bare
  `len() == w*h` assertion would silently pass. Gate script:
  `scripts/check/check-engine2d-gpu-offload-evidence.shs` (checks for
  `device_readback` provenance in the evidence harness output).
- **GUI present-loop change (GUI-5a):** `examples/06_io/ui/widget_showcase_gui.spl`'s
  native present loop moved `winit_present_rgba` out of the top of every
  `while running` iteration (which re-presented an unchanged frame every
  ~30ms tick) to (a) one present just before the loop starts and (b) one
  present inside the `if dirty:` branch, right after repacking the redrawn
  pixels — presents now happen only when the frame actually changed.
  `engine.shutdown()` on the loop's error-return path and after the loop is
  unchanged by this move.
- **Known follow-up, not yet fixed:** `as_glass_capable` on the Engine2D
  session returns nil under the interpreter (pre-existing Option-marshalling
  bug, not introduced by this landing) — `CompositorGlassCapable` impl should
  be restored once that interpreter bug is fixed; until then the glass-capable
  path is unexercised by this lane. The spec runner's metal-skip path (when no
  Metal device is available on a host) prints a `SKIP:` line rather than
  failing — keep that visibility when extending the contract spec.
- **Bulk GPU pixel upload for the deployed binary (task #28-B):** opt-in
  `SIMPLE_BULK_UPLOAD=cdylib` mode in `backend_metal.spl`'s
  `bulk_upload_u32s` stages pixels through the sibling `spl_gpu_transfer`
  cdylib (16 px/FFI call) instead of the one-call `SIMPLE_ONE_CALL_UPLOAD`
  path, because the deployed binary lacks `rt_write_u32s_to_raw`. See
  `doc/08_tracking/bug/deployed_binary_interp_extern_and_module_table_constraints_2026-07-07.md`
  for why this had to be a cdylib + inline module wiring rather than a new
  stdlib module, and for the general interpret-mode-extern /
  baked-module-table constraints behind it.

- **Current frame/font ownership correction (2026-07-14):** the canonical
  selected-font funnel is `SharedWmScene -> DrawIrComposition -> Engine2D`,
  using `shared_wm_scene_draw_ir_composition_with_content` and an Engine2D frame
  executor. The canonical SimpleOS desktop uses it. Hosted
  `HostCompositor.render_frame` still ends in
  `shared_wm_scene_render_taskbar_context_to_{backend,pixel_buffer}`, and legacy
  architecture `wm_entry.spl` targets still draw bitmap text directly. Those
  functions are compatibility renderers, not an equivalent Draw IR executor;
  migrate their frame owners rather than adding a backend-private font loader,
  atlas, cache, or draw path. Production evidence must cover the real hosted
  frame owner and retain the independent SimpleOS QEMU framebuffer crop; a
  builder-only composition fixture is supporting evidence.

- **Historical shared compatibility funnel (task #27):**
  `src/lib/common/ui/window_scene.spl` added a
  `shared_wm_scene_render_to_backend` path that consolidated titlebar/background
  paint logic before the canonical composition executor existed. It remains
  useful for bitmap compatibility and pixel-parity tests, but must not be cited
  as selected-font completion. Per-window `chrome_kind` is
  `"titled"` (default, paints the titlebar band) or `"borderless"` (no
  titlebar chrome pixels — for taskbar-like or frameless windows). Background
  painting goes through a `BackgroundSpec` provider: `kind: "color"` is
  implemented today; `"image"` / `"motion"` are reserved for later and any
  unrecognized kind fails loudly by painting the `0xFFFF00FF` marker color
  rather than silently falling back — this is intentional, not a bug, so
  don't "fix" it by adding a silent default. Gate coverage:
  `test/01_unit/lib/common/ui/window_scene_render_executor_spec.spl` (5/5,
  titled-chrome / borderless-no-chrome / color-background /
  unknown-kind-marker / cross-lane pixel-identity cases),
  `test/01_unit/os/compositor/shared_mdi_framebuffer_scene_spec.spl` (7/7),
  `test/01_unit/lib/common/ui/window_scene_draw_ir_layer_order_spec.spl`
  (2/2), and `test/03_system/check/shared_wm_renderer_unification_simple_bin_spec.spl`
  (5/5 — this spec asserts the three bridge-function symbols exist by name,
  so don't rename them without updating it).
  **Pre-existing, not touched by this landing:** `bin/simple check` on
  `window_scene_draw_ir.spl` still fails on `[x; count]` array-repeat literal
  syntax (parser gap; same failure on a clean checkout before this patch;
  also feeds bug #21). The QEMU visible-display gate still faults identically
  in the guest on a clean HEAD (freestanding module-init blocker, unrelated
  to this feature).

- **LANDED 2026-07-07 — `BackgroundSpec kind:"image"` implemented (PPM
  decode only; PNG deferred):** `BackgroundImageProvider` trait
  (`src/lib/common/ui/window_scene.spl`) is a single injected seam — the
  `common.ui` executor never decodes an image or touches the filesystem
  itself, preserving the baremetal-lane boundary. A new provider
  implementation, [src/os/compositor/background_image_provider.spl](../../../../src/os/compositor/background_image_provider.spl),
  decodes PPM (P6) via `src/lib/common/image/ppm_decode.spl`, supports
  `cover`/`contain`/`stretch`/`tile` fit modes, and keeps a content-hash
  keyed cache with stale-serve-on-decode-failure (returns the last-good
  surface rather than falling to the loud marker if a previously-decoded
  image later fails to re-read). Registration is via
  `shared_wm_scene_register_background_image_provider(provider)`, wired at
  host startup in `init_host_wm`
  (`src/os/compositor/host_compositor_entry.spl`); SimpleOS has no
  registration yet (no provider → loud `0xFFFF00FF` marker, same as any
  unrecognized kind, which is correct/intentional per the executor's
  fail-loud contract above). The reserved `"motion"` kind and the
  `WM_BACKGROUND_KIND_MOTION` constant are unchanged and still loud-fail;
  the never-implemented `MotionBackgroundSource` trait (zero implementers/
  references) was deleted as dead code during review — motion support, if
  ever built, needs a fresh contract, not this removed trait.
  Gate coverage: `test/01_unit/os/desktop/wm_background_image_provider_spec.spl`
  (8/8 — decode success, fit modes, content-hash cache hit, stale-serve on
  bad re-read, missing-file loud marker), plus the existing executor/
  compositor gates above (unaffected, still green).
  **Two interpreter bugs found during this work (not fixed, workarounds
  applied — see the bug docs for repro/detail):**
  `doc/08_tracking/bug/interp_fs_class_statics_return_result_despite_optional_types_2026-07-07.md`
  (`fs.File` statics declared `Optional`/`bool` actually return runtime
  `Result::Ok`/`Err`; `if val` on an `Err` is truthy; `File.delete` crashes
  on a stray `.path`-on-`String` access — worked around via explicit
  `match Ok/Err` and the free `file_delete` extern) and
  `doc/08_tracking/bug/interp_trait_slot_receiver_reboxed_per_call_mutation_loss_2026-07-07.md`
  (a `me`-mutating trait method called through a re-read `Trait?`-typed
  module slot gets a freshly re-boxed receiver each call, losing field
  mutations — worked around by keeping cache/stale-serve state in
  module-level `var`s, the same convention already used by the
  `_*_compositor_override_*` pattern elsewhere in this file).

- **LANDED 2026-07-07 — `BackgroundSpec kind:"motion"` implemented (manifest
  frame source, absolute-time frame selection):** `MotionBackgroundSource`
  trait (`src/lib/common/ui/window_scene.spl`) is the injected seam,
  mirroring the `kind:"image"` provider's boundary — the `common.ui` executor
  never reads a manifest or decodes a frame itself. The concrete
  implementation, [src/os/compositor/background_motion_provider.spl](../../../../src/os/compositor/background_motion_provider.spl)
  (`HostMotionBackgroundSource`), reads a small deterministic manifest (line 1
  = `frame_interval_micros`, remaining non-blank lines = ordered PPM frame
  paths), selects the current frame as a pure function of an injected
  absolute `t_micros` (no wall-clock reads inside the source — testable with
  fake time), degrades a single-frame manifest to a static image, and routes
  each resolved frame through the same content-hash cache + fit resampling
  the `kind:"image"` provider already uses (`cover`/`contain`/`stretch`/`tile`
  fit modes). Loud-fail contract matches the image provider: missing/empty
  manifest, bad interval, or empty frame set all fail construction; an
  unreadable frame with no prior good decode fails loudly at resolve time
  rather than silently falling back.
  Registration: `ensure_host_motion_background_source_registered(target_w,
  target_h)` in `src/os/compositor/host_compositor_entry.spl` gates
  registration on the env var `SIMPLE_WM_MOTION_MANIFEST` (a manifest path;
  unset ⇒ no motion source registered, no behavior change, same
  no-motion-configured contract the image provider follows) with an optional
  `SIMPLE_WM_MOTION_FIT` (defaults to `"cover"`).
  **Dirty-cadence seam:** `src/os/hosted/hosted_entry.spl`'s present loop
  calls `next_frame_due`/`shared_wm_motion_background_consume_due` to mark
  the frame dirty exactly once per due value (never per-tick) and to
  self-re-arm the source's next-due bookkeeping directly at the seam — this
  hosted chrome lane keeps the cadence honest but does **not** itself paint a
  motion frame (its `render_frame()` still direct-draws chrome only).
  **What actually animates:** the shared-MDI production lane
  (`shared_mdi_framebuffer_scene.render_shared_mdi_framebuffer_scene_for_windows`)
  has the capability, spec-proven, to resolve and blit a `kind:"motion"`
  background — but no production caller threads a non-default wall-clock `t`
  through it yet (today's callers use the default `t`), so live motion
  playback on that lane is staged future wiring, not current behavior.
  Hosted-chrome background consumption and I8 region-dirty (background-only
  re-raster instead of full-frame) are both explicitly deferred — see
  `doc/03_plan/os/desktop/wm_window_render_api_hardening_plan.md` item B
  follow-ups (1) I8 region-dirty, (2) hosted-lane consumption — and
  `doc/05_design/os/desktop/simple_gui_internal_window_impl_spec.md` for the
  I8 invariant definition.
  Gate coverage: `test/01_unit/os/desktop/wm_background_motion_provider_spec.spl`
  (10/10 — construction loud-fails, absolute-time frame advance, exactly-once
  dirty per due value, single-frame degrade-to-static, content-hash cache
  reuse, resolve-time loud-fail, executor-level pixel-diff across `t`,
  production-wrapper pixel-diff across `t`, no-spurious-epoch-fire, self-
  re-arm across 2 intervals), plus the existing image/executor/compositor
  gates above (unaffected, still green: image 8/8, executor 5/5, shared-MDI
  7/7, `shared_wm_renderer_unification_simple_bin_spec.spl` 5/5).
  **New interpreter bug found during this work (not fixed, workaround
  applied):**
  `doc/08_tracking/bug/interp_expect_inline_equality_arg_misevaluates_2026-07-07.md`
  — `expect(a == b).to_equal(false)` on two distinct `u32`s reports "expected
  A to equal B" instead of evaluating the `==` to a bool first (same family
  as the chained-methods landmine); worked around with an intermediate
  `val eq = a == b` before the `expect`.

## Session update 2026-07-18

**Glass desktop screendump progress (SimpleOS x86_64):** first non-black 
capture achieved (12.64% non-background pixels), fault storm reduced from 81 
faults to 1 after NVMe/interpreter fixes; remaining fault = nil indirect call 
in render_commands (C8 lane debugging in progress).

### Recent (2026-07-18) Knowledge Links

**Heap exhaustion root cause:** `render_baremetal_first_frame` first-frame 
allocates repeated 8MB offscreen surfaces via `rt_array_repeat`; immediate 
fix = reuse one embedded software surface across frames to keep heap footprint 
constant.

**Probe-gate convention (baremetal kernel code):** per-file 
`fn _probe_debug() -> bool: false` in freestanding kernel code modules; 
module-global `val` initializers unreliable on baremetal lanes, so use 
function-scoped probes with compile-time false defaults.

**Log-retention policy for render traces:** 
[doc/07_guide/infra/logging/log_retention_policy.md](../../../../doc/07_guide/infra/logging/log_retention_policy.md) 
converts probe/perf logs to level-gated output; never delete historical logs, 
only gate verbosity. This applies to render-performance tracing and fault 
diagnostics.

## Session update 2026-07-19 (Aqua theme + px blitter hardening)

**Aqua Mac-glass theme landed (2248995c72d):**
`wm_chrome_theme_defaults()` in
[src/lib/common/ui/wm_chrome_theme.spl](../../../../src/lib/common/ui/wm_chrome_theme.spl)
is the real single source of truth for the baremetal WM boot path's
default palette — it now returns a classic Aqua-light palette (soft
blue-gray desktop, `#F2F2F2` window bodies, glossy-blue focused
titlebars, dark text) instead of the old dark-slate default. New
`AQUA_*` tokens + `aqua_light()`/`aqua_dark()` registry factories added in
[src/lib/common/ui/glass/theme.spl](../../../../src/lib/common/ui/glass/theme.spl)
and
[src/lib/common/ui/glass/numeric_tokens.spl](../../../../src/lib/common/ui/glass/numeric_tokens.spl).
Both chrome routes retargeted: the CSS/scene backend in
[src/lib/common/ui/window_scene_draw_ir.spl](../../../../src/lib/common/ui/window_scene_draw_ir.spl)
and the hosted-compositor route in
[src/os/compositor/host_compositor_core.spl](../../../../src/os/compositor/host_compositor_core.spl)
(plus `src/os/compositor/shared_mdi_framebuffer_scene.spl`) — 10
accent-fill sites retargeted to `title_focused` so dark text never sits
on saturated blue.

**Field-order landmine — explicitly checked and clear this time:**
`WmChromeColors` field order was verified unchanged by this change (no
offset-shift risk). This struct is read positionally at multiple
construction sites across both chrome routes; ANY future edit to its
field list MUST redo that same check, since a silent reorder would
corrupt every positional construction site without a compile error.
`wm_chrome_theme_spec` was updated to the new default contract.
**Existing bitmap-evidence baselines pinned to the old dark-slate palette
will need refresh** after visual verification — expect this gate to look
"changed" for the right reason, not as a regression.

**px blitter hardening (`_px_draw_text`):** the pixel-buffer text
blitter every WM chrome route funnels through, in
[src/lib/common/ui/window_scene_draw_ir.spl](../../../../src/lib/common/ui/window_scene_draw_ir.spl)
(around line 259), now reads text via `.bytes()` + an i64 bit-test
instead of `char_code_at` / native `!=`, working around the two
freestanding-lane miscompiles documented in
[native_char_code_at_tag_shift_2026-07-19.md](../../../../doc/08_tracking/bug/native_char_code_at_tag_shift_2026-07-19.md).
Same recipe family as the rasterizer fix in `spl_fonts.spl` — see the new
[vector_fonts](../../feature_expert/vector_fonts/skill.md) feature expert
for the full landmine list this and the rasterizer both work around.

**Do NOT yet cite as landed:** `engine.spl`'s
`engine2d_default_font_config_for` execution-target pin (routes around
the broken enum `==`, see
`native_enum_eq_always_false_freestanding_2026-07-19.md`) and a
glyph-cache null-deref fix are still IN FLIGHT as of this update — check
origin before citing either as shipped.

## Session update 2026-07-20 (theme token derivation, THEME.CSS boot path, host-GPU image retention, cpu_simd honesty)

- **Aqua chrome palette now derives from `AQUA_LIGHT_*` tokens (single
  source, `e62ea541c93`):** `wm_chrome_theme_defaults()` in
  [src/lib/common/ui/wm_chrome_theme.spl](../../../../src/lib/common/ui/wm_chrome_theme.spl)
  no longer hand-copies hex literals — every field routes through a new
  `_wm_argb(rgb: u64, alpha: u64) -> u32` helper over
  `AQUA_LIGHT_DESKTOP_BG/TASKBAR/TEXT/TITLEBAR_FOCUSED/TITLEBAR_UNFOCUSED/
  SHADOW_A/SURFACE/ELEVATED/ACCENT` + `GLASS_BTN_CLOSE`
  (`common/ui/glass/numeric_tokens.spl`), probe-verified byte-identical to
  the 2026-07-19 Aqua landing. One field, `command_lane`, has NO
  `AQUA_LIGHT_*` counterpart and stays a literal by design — don't "fix"
  that by inventing a token.
- **THEME.CSS boot allowlist landed (`021b88ba0fd`), but application is
  still dead in-guest:** the VFS boot loader now allowlists `/THEME.CSS` in
  BOTH places it must appear — `_vfs_boot_dirent_matches_short_name_raw`
  (raw FAT32 dirent byte match) AND `_vfs_boot_short_name_for_path`
  (path→short-name map) in
  [src/os/services/vfs/vfs_boot_init.spl](../../../../src/os/services/vfs/vfs_boot_init.spl).
  Missing either one silently fails the load. OVMF-verified the file now
  loads (`theme bytes=1276 loaded=1`), but the parsed theme never reaches
  the render path — filed as
  `doc/08_tracking/bug/wm_theme_css_loaded_not_applied_2026-07-20.md`
  (OPEN; suspects: `wm_chrome_colors_from_css_text` parse falling back to
  defaults in-guest, or a stale pre-registration snapshot of
  `wm_chrome_theme()`).
- **Titlebar gradient attempt REVERTED, root cause filed, not fixed:** a
  per-row DrawIR gradient in `_wm_draw_ir_window_batch`
  (`window_scene_draw_ir.spl`) produced the correct color OUTSIDE a
  `while` loop but a wrong (pure black) color INSIDE it, despite identical
  source values each iteration — a freestanding-lane scalar-spill codegen
  bug, not a logic bug in this function. Filed
  `doc/08_tracking/bug/native_scalar_spill_clobber_loop_intervening_calls_2026-07-20.md`
  (same family as the 2026-07-19 tuple-spill bug, generalized from tuples
  to plain u32 scalars and from one intervening call to repeated calls
  across loop iterations — also indexed in the
  [backend](../../layer_expert/backend/skill.md) layer expert). Current
  code is back to the single flat titlebar box (unchanged behavior) with
  an in-code comment recording the investigation — do not re-attempt the
  gradient without new pixel evidence.
- **Host-GPU image-resource retention (`42de88d527c`):**
  capability-negotiated over the existing SimpleOS host-GPU IVSHMEM
  protocol
  ([src/lib/common/gpu/simpleos_host_gpu_protocol.spl](../../../../src/lib/common/gpu/simpleos_host_gpu_protocol.spl),
  wire offsets 280/288 = `REQUESTED_CAPABILITY_MASK`/
  `NEGOTIATED_CAPABILITY_MASK`, both sides clear-before-read so a stale
  nonzero from an old binary can never leak in). When negotiated, the
  guest sends a 72-byte reference (id + checksum, no pixels) for an
  unchanged image instead of the full bitmap (99.6% saved on a 64x64
  icon); the host keeps a revision table and FAILS CLOSED
  (`SIMPLEOS_HOST_GPU_REASON_UNKNOWN_IMAGE_RESOURCE`) on an unrecognized
  ref. A capability is honored ONLY when both sides freshly asserted it in
  the SAME HELLO round — an old/new protocol mix falls back to the full
  path automatically, never a silent corruption. Consumed by
  [src/os/compositor/engine2d_wm_frame_executor.spl](../../../../src/os/compositor/engine2d_wm_frame_executor.spl)
  (also noted in the [os_compositor](../../layer_expert/os_compositor/skill.md)
  layer expert).
- **`cpu_simd` is an honest scalar alias, not a SIMD backend
  (`04b3dddb3c0`):** probe/display/gate text for the `cpu_simd` Engine2D
  backend now says so explicitly (`backend_probe.spl`, `engine.spl`,
  `helpers_availability.spl` under
  [src/lib/gc_async_mut/gpu/engine2d/](../../../../src/lib/gc_async_mut/gpu/engine2d/))
  — `CpuBackend.create_simd()` builds the identical scalar `CpuBackend`;
  the x86 SSE2/AVX2 row externs exist in the runtime but are unwired
  (orphaned `CpuSimdSession`). Bug doc
  `doc/08_tracking/bug/cpu_simd_mutable_array_extern_wiring_2026-05-31.md`
  stays OPEN with a dated status note — this landing is a
  truth-in-messaging fix only, not a functional fix. Do not cite
  `cpu_simd` as a perf lever (e.g. for the `SIMPLE_GUI_BACKEND` knob above)
  until that bug is closed.

## Update Rule

After research, requirements, architecture, design, implementation,
verification, or release work changes this feature area, add or refresh
links here BEFORE committing, so the next agent starts from the current
project state.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`
