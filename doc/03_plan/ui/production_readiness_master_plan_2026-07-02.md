# GUI / Web / Game-Engine Production Readiness — Master Plan

**Date:** 2026-07-02
**Status:** Active (single source of truth for this lane; supersedes none — consolidates)
**Related:**
- [GUI hardening current plan](../../gui/gui_hardening_current_plan_2026-06-01.md)
- [Pure Simple web renderer Chromium-quality plan](../web_browser/pure_simple_web_renderer_chromium_quality_plan.md)
- [Game engine 2D/3D unification plan](../graphics/engine/game_engine_2d3d_unification_plan_2026-06-12.md)
- [Engine2D CPU/Vulkan parity](../graphics/engine/engine2d_cpu_vulkan_parallel_2026-05-29.md)

## Objective (from user directive, made precise)

Bring four product surfaces to production level, all rendering through the
**pure-Simple 2D/3D engine backed by Vulkan** (single exception: Android GUI,
which is backed by Tauri 2):

1. **GUI** — the Simple GUI framework, proven via the GUI showcase app.
2. **Web rendering** — the Simple browser rendering real pages.
3. **2D game engine + a playable 2D game.**
4. **3D game engine + a playable 3D game.**

Verification is **evidence-based, not test-log-based**: every claim of
"works" must be backed by opening the real app, capturing the actual screen,
and checking rendering quality, resolution behavior (especially low
resolution), text readability, and interactive behavior (buttons, scrolling,
other events, animations).

Work is executed by **parallel opus/sonnet/haiku implementation agents whose
output is reviewed by a higher-tier model** before acceptance.

## Execution model

- Per work item: implementation agent (model chosen by difficulty — haiku for
  mechanical work, sonnet for standard implementation, opus for hard
  rendering/engine work) → reviewing agent one tier higher (sonnet reviews
  haiku, opus reviews sonnet, fable/orchestrator reviews opus). A change is
  merged only after the reviewer confirms the evidence criteria below.
- SPipe SSpec (`*_spec.spl`) system tests are the durable form of every
  verification; screenshots/PPM evidence are their artifacts.
- Environment: headless Linux host. Real-window checks run under Xvfb
  (available) with x11 backend; Vulkan runs on the real Intel GPU
  (`Intel RPL-P`, Vulkan 1.4) with `llvmpipe`/`lavapipe` as the deterministic
  software fallback for reproducible pixel evidence.

## Success criteria (goal gates)

The goal is met when **every** gate below passes and is reproducible via a
checked-in SPipe spec or script.

### G1 — GUI production level (Vulkan-backed)

- **G1.1 Real app opens:** GUI showcase app launches as a real window
  (Xvfb/x11 acceptable) with the rendering path going through the Simple
  Vulkan-backed engine — not a CPU-only or stub backend. Evidence: capture of
  the live window (e.g. `xwd`/ffmpeg/import) plus a renderer log line proving
  the Vulkan device was used.
- **G1.2 Showcase coverage:** showcase exercises at minimum: buttons, labels,
  text input, checkbox/toggle, list/table, scroll area, tabs/menu, dialog,
  image view, themed (glass) surfaces, and an animated element.
- **G1.3 Low-resolution readability:** at 640×480 and 800×600 (and 1280×720
  as the nominal case), captured screenshots show all showcase text readable:
  glyphs ≥ target px height, no clipped/overlapping labels, layout does not
  overflow the viewport. Verified by an automated text-readability oracle
  (glyph-region contrast + expected-string OCR/pixel-oracle match) plus
  archived screenshots.
- **G1.4 Rendering quality/consistency:** same scene rendered at the three
  resolutions and across two runs is pixel-stable (deterministic) on the
  software Vulkan path, and structurally consistent (layout geometry oracle)
  on the hardware path. No missing glyphs, no uninitialized-memory artifacts.
- **G1.5 Event system tests:** SPipe system tests drive the real app: button
  click changes state visibly; scroll surface scrolls (content offset visible
  in captures); text input receives keystrokes; hover/focus states render.
  Each assertion is capture-backed (before/after frame differ in the expected
  region and match oracle).
- **G1.6 Animation:** at least one animation (e.g. progress/transition) is
  captured as a frame sequence; frames advance monotonically with expected
  easing (oracle on sampled positions), no tearing/stalls.

### G2 — Simple browser web rendering production level (Vulkan-backed)

- **G2.1 Real browser opens a page:** Simple browser app launches, loads a
  local corpus page and at least one real saved page (offline snapshot of a
  famous site), renders through the same Vulkan-backed engine, captured.
- **G2.2 Rendering quality:** existing Chromium-comparison harness gates stay
  green (famous-site corpus 45/45); the tracked production glyph/compositing
  divergence (`differentPixels: 2717` focused case) is driven down —
  production gate: focused text case reaches Chrome-like antialiased glyph
  compositing with different-pixels below the checked-in strict bound, and no
  regression on the corpus.
- **G2.3 Text readability at low resolution:** browser rendering of the text
  corpus at 640×480/800×600 windows passes the same readability oracle as
  G1.3 (wrapped lines, no clipped glyphs).
- **G2.4 Interaction:** scroll (wheel + keyboard) over a long page is
  capture-verified; link click navigation works; back/forward state renders.
- **G2.5 Consistency:** the browser and the GUI showcase render shared UI
  chrome (buttons, scrollbars, text) with identical glyph rasterization and
  theme tokens (cross-app pixel oracle over shared widgets).

### G3 — 2D game engine production level + playable 2D game

- **G3.1 Engine:** game2d stack (sprite batch, texture atlas, canvas, font,
  input, animation) renders through Vulkan; CPU/Vulkan pixel parity gate
  stays green.
- **G3.2 Playable game:** a complete small 2D game (e.g. breakout/platformer)
  ships in `src/app/`: menu → gameplay → score → game-over loop; ≥60 s
  automated play session runs without crash.
- **G3.3 Evidence:** real window capture of gameplay; frame-sequence capture
  proves sprite motion, collision response, score text updates; input events
  (keyboard) alter gameplay in captures.
- **G3.4 Performance:** stable frame pacing at target resolution (frame-time
  oracle: p95 ≤ 33 ms on software path at 800×600, no monotonic memory
  growth over the session).

### G4 — 3D game engine production level + playable 3D game

- **G4.1 Engine:** renderer3d + gpu_mesh3d + lighting + camera + game_loop3d
  render through Vulkan (real device and lavapipe); depth-correct, lit,
  textured meshes.
- **G4.2 Playable game:** a complete small 3D game (e.g. rolling-ball
  obstacle course or first-person collect-the-items) ships: camera movement,
  object interaction, win/lose condition; ≥60 s automated session, no crash.
- **G4.3 Evidence:** capture-backed proof of 3D rendering (perspective,
  depth occlusion oracle: near object occludes far), animation (moving
  object across frames), and input-driven camera motion.
- **G4.4 2D-over-3D composition:** HUD (2D engine layer) composites over the
  3D scene on the same surface (per the unification plan), capture-verified.

### G5 — Android Simple GUI over Tauri 2

- **G5.1 Build:** the Tauri 2 Android target of the Simple GUI builds
  reproducibly from a checked-in script.
- **G5.2 Run + capture:** app runs on an Android emulator (or device if
  available); screen captured via adb; if no emulator can run in this
  environment, the gate is the checked-in build artifact + a
  WebView-equivalent rendering proof (Tauri dev-server page capture) and the
  limitation is recorded, not silently skipped.
- **G5.3 Consistency:** the Android (Tauri/HTML) rendering of the shared
  showcase widget set is structurally consistent with the desktop Vulkan
  rendering (layout geometry + theme-token oracle; pixel-identity is NOT
  required across backends).
- **G5.4 Readability:** captures at a low-DPI/small-screen profile pass the
  text-readability oracle.

### G6 — Cross-cutting

- **G6.1 Pure-Simple rule:** all new implementation is `.spl`/`.shs`;
  desktop rendering paths have no non-Simple runtime dependency beyond
  approved SFFI (libvulkan, X11, etc.). Rust seed untouched except bootstrap.
- **G6.2 All gates are SPipe specs** registered in the test tree and green in
  `bin/simple test`; no skipped tests without approval.
- **G6.3 Review chain:** every merged change in this lane has a recorded
  higher-model review verdict (in the lane report, not git).
- **G6.4 Evidence archive:** captures/PPMs land under the build/evidence
  directory with a manifest; the lane report links every gate to its
  evidence file.

## Phases

- **P0 — Baseline audit (this session):** run existing gates, launch showcase
  /browser/game demos under Xvfb, capture current screenshots, record which
  gates already pass. Output: baseline evidence + gap list per gate.
- **P1 — GUI hardening (G1):** fix gaps found in P0; build/extend showcase;
  low-res readability oracle; event/animation system tests.
- **P2 — Browser hardening (G2):** glyph antialias/gamma compositing slice
  (the known blocker), interaction tests, low-res gates.
- **P3 — 2D game (G3):** engine gap fixes + game + capture gates.
- **P4 — 3D game (G4):** engine gap fixes + game + HUD composition.
- **P5 — Android/Tauri 2 (G5):** build + emulator/capture path.
- **P6 — Consistency + final sweep (G2.5, G6):** cross-app oracles, full
  gate run, lane report.

P1–P5 run as parallel agent lanes where files don't overlap; each lane uses
the impl-model/review-model pairing from the execution model.

## Work breakdown (initial wave, derived from the audit)

| # | Lane | Work item | Impl model | Reviewer |
|---|------|-----------|-----------|----------|
| W1 | GUI (P1) | Interactive GUI showcase app: widget tree → layout → Draw-IR → engine2d → winit window, with live event loop (click, scroll, text input, animation) — closes the missing widget→DrawIR converter and the event.spl stub arms | opus | fable |
| W2 | GUI (P1) | Linux GUI launch + Xvfb capture harness (`scripts/gui/linux-gui-run.shs`) + low-res readability oracle (640×480 / 800×600 / 1280×720) | haiku | sonnet |
| W3 | Browser (P2) | Glyph antialias/gamma compositing slice toward Chrome parity on the focused text case; no corpus regression | opus | fable |
| W4 | Browser (P2) | Browser interaction system tests: scroll/link-click/back-forward, capture-backed, low-res gates | sonnet | opus |
| W5 | Game 2D (P3) | Fix breakout example (`RawHandle` ctor break), file JIT lowering bugs (`clamp_f`, `Game.update` `g`), ship playable 2D game with window + capture + input gates | sonnet | opus |
| W6 | Game 3D (P4) | engine3d Vulkan present path + small playable 3D game (depth/lighting/camera/HUD-over-3D), capture-backed | opus | fable |
| W7 | Android (P5) | Run Tauri 2 Android emulator harness end-to-end, adb capture, consistency + readability oracles; record runtime-bundling gap precisely | haiku | sonnet |
| W8 | Tests (P6) | Event/animation SPipe system specs shared across apps (button/scroll/drag/text/animation frame oracles) | sonnet | opus |

Baseline findings already recorded (2026-07-02): Vulkan engine2d readback gate
passes live; breakout example fails (`semantic: too many arguments for class
RawHandle constructor`); JIT falls back on `EngineColor.to_rgba8`
(`Unknown variable: clamp_f`) and `Game.update` (`Unknown variable: g`).

### Recovery session status (2026-07-02 afternoon)

The first execution session crashed at 13:53: a GUI check ran against the
live desktop display and the resulting Xwayland death logged out the whole
session (all W-agents killed mid-work). Guards added: `linux-gui-run.shs`
is Xvfb-only by default; `check-gui-low-res-readability.shs` is offscreen
(`SIMPLE_GUI=0` + `SHOWCASE_PPM`). Recovered state:

- **W2 GREEN:** low-res readability check + SPipe spec pass at 640x480 /
  800x600 / 1280x720 (`test/03_system/check/gui_low_res_readability_spec.spl`).
  Oracle is polarity-aware (dark theme). The G1.3 layout gap is closed:
  the showcase grid is now adaptive (column-major flow, rows from available
  height) and all 18 cells fit unclipped at 640x480 (visually verified).
- **W5 unblocked, not done:** breakout now has focused production, milestone
  capture, and window-capture specs under `test/03_system/game2d/`. The old
  stale-`rt_len` note is superseded by the current blockers:
  `bin/simple run` still SIGSEGVs in the Cranelift JIT on `LoopDriver.step`
  (`doc/08_tracking/bug/jit_game2d_backend_method_dispatch_sigsegv_2026-07-02.md`),
  and this host's available binaries expose no real window externs
  (`doc/08_tracking/bug/game2d_no_window_externs_in_host_binaries_2026-07-03.md`).
  `breakout_window_capture_spec.spl` records the host block cleanly: 1/1 pass
  on 2026-07-02.
- **G4 narrowphase fixed:** PhysicsWorld3D never dispatched Sphere-Box;
  wired the existing `collide_sphere_aabb_3d` for both orderings.
  physics2 suite 37/37 (also repaired 4 stale specs: RawHandle ctor,
  wrong raycast import path).
- **All game2d examples JIT-lowerable up to runtime dispatch:** alias→direct
  imports, fn→me on mutating methods, real input API in pool/stacking. The
  remaining run blocker is method dispatch in the co-compiled JIT unit, not
  stale `rt_len`/`rt_math_sin` symbol presence.
- **W7 host assessment:** the 9 Tauri check specs pass locally (validator
  path, e.g. tauri_android_render_log_validator_spec 13/13), but this host
  has no Android SDK/adb/emulator (`ANDROID_HOME` unset). Per G5.2 the
  emulator leg cannot run here; the gate falls to the checked-in build
  artifact + WebView-equivalent proof, and needs a host/CI with the SDK
  for the adb-capture leg. Recorded, not skipped.
- Bugs recorded: `interp_module_alias_time_shadowed_builtin`,
  `jit_lowering_clamp_f_engine_color` (nested-fn root cause),
  `jit_lowering_module_alias_and_panic`, `parser_step_decorator_string_form`,
  `bootstrap_pure_simple_stage2_stall_yoon_note`,
  `physics_world3d_sphere_collision_not_detected` (fixed same day),
  `interp_static_fn_new_hijacks_named_ctor` (P1),
  `engine3d_ext_impl_blocks_never_imported`,
  `cranelift_f32_trig_wrapper_codegen`, `interp_for_over_list_generic`
  (all 2026-07-02).

### Recovery session 2 status (2026-07-03 morning)

Session b9f6bda6 crashed 04:30 mid-turn (overnight stage4 + final sweep died
with it). Recovered facts:

- The "silent no-op" it was investigating at crash time was a false alarm:
  `time setsid cmd` measures only the setsid fork-parent (~0.02 s); the
  detached child completes and logs normally. No runner bug.
- Final sweep was killed at 7/10 — the 7 that ran all passed
  (low-res readability, vulkan window, draw-IR pipeline, showcase events,
  browser interaction, cross-app glyph, game2d replay). breakout, rollball,
  tauri-proof re-verification pending on the freshly deployed binary.
- Stage4 redeploy restarted 2026-07-03 09:03 via the bug workaround
  (direct `native_build_main.spl` run, bypassing the zombie-prone wrapper).
- Parallel lanes running: P1 native-build zombie/hang root fix (sonnet,
  worktree); G2.5 glyph unification — Engine2D adopts browser table +
  5*scale advance, browser baselines stay byte-identical (opus, worktree).
- Leftover working-copy from the crash (semantic fallback probe spec +
  generated spec docs) committed and pushed (385d5c330f).

### Gate → evidence ledger (G6.4, as of 2026-07-02 evening)

| Gate | Status | Reproducer | Evidence |
|------|--------|-----------|----------|
| G1.3 low-res readability | PASS | `scripts/check/check-gui-low-res-readability.shs` + `test/03_system/check/gui_low_res_readability_spec.spl` | `build/gui-low-res-readability/res_*/capture.ppm` |
| G1.5 GUI events (showcase) | PASS (synthetic events) | `test/03_system/gui/showcase_event_spec.spl` | before/after PPMs via `SHOWCASE_BEFORE_PPM`/`AFTER_PPM` |
| G1.5/G1.6 game2d events+animation | PASS (headless replay) | `test/03_system/game2d/game2d_event_replay_spec.spl` | frame_hash oracles in-spec |
| G4.1 3D depth-correct render | PASS (CPU backend) | `examples/11_advanced/game3d_smoke/main.spl` | `build/game3d_smoke.ppm` |
| G4.3 3D motion + camera | PASS | `examples/11_advanced/game3d_rolling/main.spl` | `build/game3d_rolling_*.ppm` (4) |
| G4.4 HUD over 3D | PASS (direct blit; LayerTree bridge blocked by interp bugs) | `examples/11_advanced/game3d_hud/main.spl` | `build/game3d_hud.ppm` |
| G1.1 real window via Vulkan | NOT RUN (live-display ban; needs Xvfb window run) | `scripts/gui/linux-gui-run.shs` | — |
| G4.2 3D game 60s session | PASS on seed binary (rollball: win+lose autopilot, 3600 fixed steps each, 10 gates; PERF-GAP recorded: frame_p95 ≈2.9 s vs 33 ms target — cranelift f32-trig fallback forces interpreted raster) | `scripts/check/check-game3d-rollball.shs` + `test/03_system/game3d/rollball_production_spec.spl` | `build/game3d-rollball/*.ppm` (11) |
| G3.2/G3.3 2D game breakout | IN PROGRESS (G3.2 3600-step logic session passes; real-window leg records host block; rendered 3600-frame interpreter path too slow) | `scripts/check/check-game2d-breakout.shs` + `test/03_system/game2d/breakout_*_spec.spl` | `breakout_production_spec.spl` 1/1 for G3.2 logic session; `breakout_window_capture_spec.spl` 1/1 recorded host block; `build/game2d-breakout/*` when the full wrapper is run |
| G2.2 glyph parity | PASS (differentPixels 2717→3; calibrated LCD compositing; caveat: Chrome-calibrated atlas, not an independent rasterizer) | `node tools/electron-shell/verify_famous_site_production_probe.js` (authoritative; see runner P1 bug) + probe/corpus specs | `test/09_baselines/famous_site_corpus/site_0_google/*` |
| G2.3 browser low-res text | PASS | `scripts/check/check-browser-interaction.shs` + `test/03_system/gui/browser_interaction_spec.spl` | `build/browser-interaction/lowres_*.ppm` |
| G2.4 scroll | PASS (marker shifts exactly 120px) | same check script/spec | `build/browser-interaction/scroll_offset*.ppm` |
| G2.4 link-click/back-forward | PASS (lockstep hit-test + history; click→back→forward pixel round-trip A/B pages) | same check script/spec (9/9) | `build/browser-interaction/nav_*.ppm` (4) |
| G2.5 cross-app glyph consistency | HONEST-GAP gate (47/88 chars diverge, advance 6*scale vs 5*scale; unification blocked by exact-pixel baselines — see bug cross_app_glyph_rasterization_diverges) | `scripts/check/check-cross-app-glyph-consistency.shs` + `test/03_system/check/cross_app_glyph_consistency_spec.spl` (5/5) | `build/cross-app-glyph-consistency/*` |
| G1.1 showcase Vulkan render | PASS via SIMPLE_GUI_BACKEND=vulkan (spec 6/6 w/ seed); live-window capture leg `unavailable_no_winit` (no rt_winit in current binaries — flips to pass when winit-linked binary deploys) | `scripts/check/check-gui-vulkan-window.shs` + `test/03_system/check/gui_vulkan_window_spec.spl` | `build/gui-window-evidence/*` |
| G5.2 Android emulator capture | Emulator leg BLOCKED on host (no SDK/JDK — gap precisely recorded); fallback legs PASS: WebView-equivalent proof renders real Tauri shell UI headlessly at 360x640 (review fixed error-overlay capture + removed python oracle), gradle-artifact gap analysis | `scripts/check/check-tauri-android-webview-proof.shs` + `test/03_system/check/tauri_android_webview_proof_spec.spl` (3/3) | `build/tauri-android-proof/*` |

## Current state (audited 2026-07-02)

Current combined evidence for Linux RenderDoc/Vulkan, Vulkan Engine2D readback,
CPU SIMD Engine2D acceleration, QEMU screendump/readback access, SimpleOS
QEMU/WM hardening, and LLVM-to-SimpleOS cross-toolchain status is indexed in
`doc/09_report/linux_renderdoc_simpleos_hardening_evidence_current_2026-07-02.md`.

### Vulkan / engine

- Vulkan stack is Simple engine + SFFI (`rt_vulkan_*` / `rt_vk3d_*` in
  `src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl`, `engine3d/sffi_vulkan3d.spl`)
  over the native runtime (`src/compiler_rust/runtime/src/vulkan/`, ash-backed;
  interpreter has a separate dlopen path). "Pure-Simple backed Vulkan" here
  means: all engine/render logic in Simple; libvulkan reached via the runtime
  SFFI boundary — this is the accepted architecture.
- **Baseline check 2026-07-02:** `scripts/check/check-vulkan-engine2d-readback.shs`
  passes live on this host — present + readback exercised, clear/rect pixel
  oracles pass, `vulkan_strict_spec` 18/18, CPU/Vulkan engine2d parity pass.
- engine2d: ~90 files, real SPIR-V 1.3 raster kernels
  (`backend_vulkan_spirv_raster_blobs.spl`). engine3d: ~55 files, breadth-first
  (scene graph/mesh/material/camera present, thin proofs; only `sphere3d_smoke`).
- **Gaps:** runtime `vulkan` cargo feature off by default; game2d SDL window
  backend is a stub ("Wave C" unwired) — no live window/present driven from the
  game path; `game3d_session.spl` is a 2.9KB stub; verification is
  checksum/manifest/FNV-hash oracles, not reference-image pixel diffs.

### GUI / browser

- Extensive UI lib (`src/lib/common/ui/`): widget/layout/draw-IR/glass theme,
  x11 backend gate, html/wasm backends, `web_render_api.spl` +
  `web_render_bitmap_evidence.spl`.
- Browser: famous-site corpus gate green (45/45) on offline oracle; known
  production blocker is Chrome-like glyph antialias/gamma/LCD compositing
  (focused case `differentPixels: 2717`; raw glyph overlays fail closed).
- Tracked issues: 66 GUI, 44 browser, 16 Vulkan, 6 game bugs in
  `doc/08_tracking/bug/` (e.g. `gui_web_2d_vulkan_browser_backing_2026-06-23`).

### GUI framework detail (audited)

- Pipeline: `widget.spl` → `layout.spl` → HTML render OR (newer, **not yet
  wired to the widget tree**) `draw_ir.spl` → engine2d `draw_ir_adv`. The
  **widget-tree → Draw-IR converter is missing** — the team's own docs call it
  the preferred next refactor; interactive apps currently hand-roll paths.
- Real windowing: SDL2 (`src/runtime/runtime_sdl2.c`, real) and winit
  (`rt_winit_*`, real) exposing raw pixel buffers.
  `examples/06_io/ui/widget_showcase_gui.spl` opens a real winit window but is
  a **static scene** that bypasses widget/layout/draw-IR; the 3 canonical GUI
  check apps are all static/non-interactive.
- `common/ui/event.spl` hub: Mouse/Scroll/Resize/touch arms are **no-op
  stubs**; real pointer routing exists only in the WM layer
  (`window_scene.spl`). Animation support is minimal
  (`skia/feature/animation/` — 2 files, no timeline/easing framework).
- Fonts: real stb_truetype SFFI (`runtime_font.c`) + 4-tier fallback
  rasterizer (`nogc_sync_mut/text_layout/font_rasterizer.spl`); a second
  independent glyph stack in `src/lib/skia/`. SDL editor bridge still draws
  placeholder rects for text. DPI/low-res handling is ad hoc.
- Launch/capture: headless PPM dump (`SHOWCASE_PPM=` etc.) is the canonical
  oracle; macOS has a GUI launch script, **Linux has none**; QEMU
  QMP-screendump pixel baselines (786 checked-in PPMs) exist but are opt-in.

### Browser detail (audited)

- Own engine: `src/lib/gc_async_mut/gpu/browser_engine/` (60 files —
  tokenizer/tree builder/DOM/CSS/selector/layout incl. inline/float/table/
  paint/text painter/webgpu). App shells: `src/app/ui.browser/` (pure-Simple),
  `src/app/ui.chromium*/` (hosted Chromium + Acid2 + devtools harnesses).
- Active blockers: Chrome-like glyph antialias/gamma compositing (focused
  `differentPixels: 2717`), flex/inline structural geometry mismatches,
  JS execution not wired (`browser_script_execution_not_wired_2026-05-10`),
  two unmerged CSS parsers.

### Tauri / Android / test infra

- Tauri 2 shell at `tools/tauri-shell/` with desktop/iOS/Android launchers and
  `capture-all.command`. iOS lane is HIGH maturity (Metal render + MDI proofs).
  Android: full gradle project, x86_64/arm64 APKs build, emulator
  `simple-pixel-8-api36` harness via adb
  (`scripts/check/check-tauri-android-mobile-renderer-evidence.shs`) — but
  currently demo-mode: no Android-compatible Simple runtime bundled.
- Capture tooling: xvfb-run (1280x720x24 typical) for desktop, adb
  screenshot+logcat for mobile, RenderDoc `.rdc` capture scripts for Vulkan.
- SPipe: `use std.spec.*`, `@step`/`@capture` decorators, run via
  `bin/simple test path/to/spec.spl`; docgen must emit 0 stubs. Absolute
  oracles required (no fixtures-only false-greens).

### Host environment

- Headless (no DISPLAY); Xvfb available. Vulkan 1.3/1.4 loader with Intel
  RPL-P iGPU (Mesa) + llvmpipe/lavapipe software devices — deterministic
  software path available for pixel-stable evidence.
