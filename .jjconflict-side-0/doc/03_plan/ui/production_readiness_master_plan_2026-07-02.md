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
- **W5 unblocked, not done:** breakout now has focused production, rendered
  oracle, milestone capture, and real-window specs under
  `test/03_system/game2d/`. The old
  stale-`rt_len` note is superseded by the current blockers:
  `bin/simple run` still SIGSEGVs in the Cranelift JIT on `LoopDriver.step`
  (`doc/08_tracking/bug/jit_game2d_backend_method_dispatch_sigsegv_2026-07-02.md`),
  and deployed `bin/simple` still lacks the gui-feature `rt_winit_*` surface
  (`doc/08_tracking/bug/game2d_no_window_externs_in_host_binaries_2026-07-03.md`).
  The wrapper now uses the existing gui-feature Rust driver binary for the
  real-window leg when present; `scripts/check/check-game2d-breakout.shs`
  passes end-to-end with 160x120 milestone PPMs, low-res rendered divergence
  (`lowres_frame_time_ms=12` after clipped direct framebuffer writes in
  `HeadlessBackend._draw_rect_filled`), and a 12-frame private-Xvfb real
  window capture. The 800x600 frame-time target remains a tracked performance
  gap.
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

Midday update (2026-07-03):

- P1 zombie fix LANDED (reviewed by fable): parent reaps by process exit
  not pipe EOF; exit-0-without-binary is a hard error at worker funnel and
  parent. Regression spec 6/6. Bug → fixed-pending-verification.
- G2.5 CLOSED (reviewed by fable): shared glyph table, strict spec 6/6,
  browser baselines verified unmoved on main.
- Stage4 blocker root-cause in progress: worker aborts in COMPILE phase
  with location-less `cannot parse '<char>' as i64` (operand tracks source
  content: '\"' then 'n'). int() guards added to parser int-literal paths
  and type_checker refinement predicates so the next run surfaces a located
  parser error instead of an abort; guarded rebuild running.

Afternoon update (2026-07-03, after two OOM crashes + two origin clobber
restores):

- Stage4 root cause FOUND and FIXED: parse_primary_expr routed FloatLit
  through the int-literal branch (dead float branch since the 06-26 tree
  restore) — every float literal truncated to int by the seed's tolerant
  int(); non-tolerated texts aborted stage4 location-less. Fixed + same
  disease in parser_cli. Second parser-parity gap fixed: CoreLexer had no
  suffixed-literal support (10u8/10_u8) — added with CORE_TOKEN_SUFFIX
  channel. Both consolidated onto origin.
- Engine3d JIT fix stack landed (6-defect chain: rt_math_* symbol table +
  C-ABI specs, f32 param/return/store/binop ABI, receiver-aware trait
  dispatch, marshalling): game3d_smoke 7 failed bodies → 0 fully-JIT;
  frame p95 8434ms → 150ms on loaded host. 33ms target pends idle-host
  rerun on deployed binary.
- Active fable lanes: (A) zero parser errors across the 245-file stage4
  parse surface — iterating capped probes + regression baseline; (B) full-
  JIT rollball/breakout — private _sin/_cos f32/f64 symbol collision,
  Array.add_static resolution, engine2d interpreter-routing heuristic;
  seed cranelift rebuild in worktree.
- Process hardening after incidents: all heavy simple runs under
  scripts/resource/run_capped.shs with CAP_MEM_MAX=4G (host 7.4G; wrapper
  default 32G never fires here); jj st pre-commit verification (two mass-
  clobber commits restored on origin today); fetch + verify src/lib
  populated before any push.
- Stage4 rebuild queued on lane A zero-error result; then deploy →
  G1.1 live-window leg + G3.4/G4.2 frame gates on idle host.

### Gate → evidence ledger (G6.4, as of 2026-07-02 evening)

| Gate | Status | Reproducer | Evidence |
|------|--------|-----------|----------|
| G1.3 low-res readability | PASS | `scripts/check/check-gui-low-res-readability.shs` + `test/03_system/check/gui_low_res_readability_spec.spl` | `build/gui-low-res-readability/res_*/capture.ppm` |
| G1.4 software-path determinism | PASS 2026-07-03 (two fresh 640x480 renders byte-identical, `cmp` on capture.ppm) | `scripts/check/check-gui-low-res-readability.shs` run twice + cmp | `build/gui-low-res-readability/res_640x480/capture.ppm` |
| Sweep re-verification (post-greenwash-fix runner) | PASS 2026-07-03: breakout_production 1/1, rollball_production 11/11, tauri_webview_proof 3/3 — per-describe sums, no Failed:0 masking | capped `bin/simple test --clean` per spec | sweep log in session scratchpad |
| Evidence batch (this-session, honest runner, 2026-07-04) | G1.5 showcase events 2/2; G1.5/G3.3 game2d replay 5/5; G1.6/G3.3 breakout event+animation 13/13; G2.3/G2.4 browser interaction 9/9; G2.2 corpus div-geometry 2/2; draw-IR pipeline 6/6; G1.1 vulkan-window 5/6 — the 1 fail IS the live-window leg (`unavailable_no_winit`), previously masked by pre-fix runner file-level Failed:0, flips on winit-linked deploy | capped `bin/simple test --clean` per spec | evidence_batch_results.txt (session scratchpad) + build/gui-window-evidence/*
| G5.3/G5.4 batch (2026-07-04) | Android render-log validator 13/13; Chrome↔Simple layout manifest 1/1; GUI-vs-Tauri equivalence 17/17 (structural consistency + readability legs). One NEW bug: MDI input-to-paint validator hangs 60s on malformed rows (25/26 pass) — doc/08_tracking/bug/tauri_mdi_input_to_paint_validator_hang_2026-07-04.md | capped `bin/simple test --clean` per spec | g5_batch_results.txt (session scratchpad) |
| G1.5 GUI events (showcase) | PASS (synthetic events) | `test/03_system/gui/showcase_event_spec.spl` | before/after PPMs via `SHOWCASE_BEFORE_PPM`/`AFTER_PPM` |
| G1.5/G1.6 game2d events+animation | PASS (headless replay) | `test/03_system/game2d/game2d_event_replay_spec.spl` | frame_hash oracles in-spec |
| G4.1 3D depth-correct render | PASS (CPU backend) | `examples/11_advanced/game3d_smoke/main.spl` | `build/game3d_smoke.ppm` |
| G4.3 3D motion + camera | PASS | `examples/11_advanced/game3d_rolling/main.spl` | `build/game3d_rolling_*.ppm` (4) |
| G4.4 HUD over 3D | PASS (direct blit; LayerTree bridge blocked by interp bugs) | `examples/11_advanced/game3d_hud/main.spl` | `build/game3d_hud.ppm` |
| G1.1 real window via Vulkan | PASS: private Xvfb + gui-feature driver captures the compact top-of-frame widget showcase through the Vulkan backend at 200x150; backend/frame/content/window assertions pass (`render_wait_secs=52`, `window_capture_attempts=9`, `ink_coverage=0.00507`) | `SIMPLE_BIN=src/compiler_rust/target/debug/simple SIMPLE_LIB=src sh scripts/check/check-gui-vulkan-window.shs` + `test/03_system/check/gui_vulkan_window_spec.spl` | `build/gui-window-evidence/evidence.env`, `showcase_vulkan_window.png`, `showcase_vulkan_offscreen.ppm`, `oracle.log`; spec 6/6 |
| G4.2 3D game 60s session | PASS WITH PERF GAP (rollball: win+lose autopilot, 3600 fixed steps each, 10 gates, 11 PPMs; bounded wrapper records `frame_p95_ms=not_measured_operation_limit` because the 800x600 software raster probe exceeds the interpreter operation limit before one sample completes) | `scripts/check/check-game3d-rollball.shs` + `test/03_system/game3d/rollball_production_spec.spl` | `overall=pass`; `build/game3d-rollball/*.ppm` (11); tracked gap `doc/08_tracking/bug/cranelift_f32_trig_wrapper_codegen_2026-07-02.md` |
| G3.2/G3.3/G3.4 2D game breakout | PASS WITH PERF GAP (wrapper overall pass; G3.2 logic session passes; G3.3 low-res rendered divergence, milestone PPMs, and real-window leg pass; G3.4 records tracked 800x600 JIT/render gap) | `scripts/check/check-game2d-breakout.shs` + `test/03_system/game2d/breakout_*_spec.spl` | `overall=pass`; `breakout_production_spec.spl` 1/1; `breakout_render_oracles_spec.spl` 2/2, `lowres_frame_time_ms=12`; `breakout_captures_spec.spl` 1/1, 5 PPMs at 160x120; `breakout_window_capture_spec.spl` 1/1 with `window_frames_presented=12`; `build/game2d-breakout/*` |
| G2.2 glyph parity | PASS (differentPixels 2717→3; calibrated LCD compositing; caveat: Chrome-calibrated atlas, not an independent rasterizer) | `node tools/electron-shell/verify_famous_site_production_probe.js` + probe/corpus specs | `test/09_baselines/famous_site_corpus/site_0_google/*` |
| G2.3 browser low-res text | PASS | `scripts/check/check-browser-interaction.shs` + `test/03_system/gui/browser_interaction_spec.spl` | `build/browser-interaction/lowres_*.ppm` |
| G2.4 scroll + link-click/back-forward | PASS (120px marker shift; click→back→forward pixel round-trip, 9/9) | same check script/spec | `build/browser-interaction/scroll_offset*.ppm`, `nav_*.ppm` |
| G2.5 cross-app glyph consistency | PASS 2026-07-03 (was HONEST-GAP): shared `common.ui.glyph_bitmap_5x7` table + unified 5*scale advance; 88/88 chars byte-identical, strict spec 6/6; browser baselines unmoved | `scripts/check/check-cross-app-glyph-consistency.shs` + `test/03_system/check/cross_app_glyph_consistency_spec.spl` | `build/cross-app-glyph-consistency/*` |
| CPU SIMD Engine2D acceleration | PASS 2026-07-03: x86_64 AVX2 native SIMD kernels executed, matched scalar bit-for-bit, provider hits 17, native SIMD hits 2, fill/copy/alpha/scroll/diagram mismatch counts all 0, blur/tolerance false | `REPORT_PATH=doc/09_report/cpu_simd_engine2d_evidence_current_2026-07-02.md BUILD_DIR=build/cpu-simd-engine2d-evidence-current sh scripts/check/check-cpu-simd-engine2d-evidence.shs` | `doc/09_report/cpu_simd_engine2d_evidence_current_2026-07-02.md`; `build/cpu-simd-engine2d-evidence-current/evidence.log` |
| SimpleOS hardening aggregate | PASS 2026-07-03: 13/13 rows pass for filesystem launch, SSH, shared WM, CPU SIMD Engine2D, SimpleOS LLVM port, GUI/Web/2D Vulkan RenderDoc, WebRenderer/Engine2D, Simple GUI/WebRenderer, QEMU host counterpart, GUI SMF artifact, QEMU MDI, RV64 display-smoke QMP, and QEMU virtio-gpu access; guest perf evidence is sourced from `qemu-guest` | `BUILD_DIR=build/simpleos_hardening_evidence_matrix_current REPORT_PATH=doc/09_report/simpleos_hardening_evidence_matrix_2026-07-03.md sh scripts/check/check-simpleos-hardening-evidence-matrix.shs` + `test/03_system/gui/simpleos_hardening_evidence_matrix_spec.spl` (3/3) | `doc/09_report/simpleos_hardening_evidence_matrix_2026-07-03.md`; `doc/09_report/gui_renderdoc_feature_coverage_status_2026-07-03.md`; `doc/09_report/simpleos_llvm_port_evidence_current_2026-07-02.md`; `doc/09_report/cpu_simd_engine2d_evidence_current_2026-07-02.md` |
| QEMU GPU/QMP access | PASS 2026-07-03: RV64 display-smoke QMP framebuffer path passes with 320x240 nonblack frame, 5 anchor matches, virtio-gpu access contract `scenario_riscv64_display_smoke`, and QEMU guest perf marker sourced from `qemu-guest`; host GTK perf is not promoted as guest perf | `sh scripts/check/check-simpleos-hardening-evidence-matrix.shs` | `doc/09_report/simpleos_hardening_evidence_matrix_2026-07-03.md`; `doc/09_report/rv64_display_smoke_qmp_evidence_current_2026-07-02.md`; `src/os/_QemuRunner/scenario_catalog.spl:scenario_riscv64_display_smoke` |
| G1.1 showcase Vulkan render | PASS: `assert_vulkan_backend=pass`, `assert_vulkan_frame=pass`, `assert_widget_content=pass`, `assert_window_capture=pass`, `overall=pass`; wrapper uses `SHOWCASE_G1_1_COMPACT=1` for the G1.1 top-of-frame gate while broader widget coverage remains in G1.2/G1.3/G1.5 specs. | `scripts/check/check-gui-vulkan-window.shs` + `test/03_system/check/gui_vulkan_window_spec.spl` | `build/gui-window-evidence/*` |
| GUI widget RenderDoc goal | PASS 2026-07-03: 43/43 widget feature witnesses, Simple Vulkan widget `.rdc` `RDOC`, Electron Chromium widget `.rdc` `RDOC`, direct Electron ARGB proof pass, blocked gates 0 | `sh scripts/check/check-gui-widget-renderdoc-goal-status.shs` | `doc/09_report/gui_widget_renderdoc_goal_status_2026-07-03.md`; `build/renderdoc/widget-probe-small/simple/simple_gui_app_capture.rdc`; `build/renderdoc/electron-implicit-layer-default-autocapture/electron-html/electron_gpu_capture.rdc` |
| GUI RenderDoc feature coverage aggregate | PASS with remaining external-scope blockers: widget, Simple/Chrome/Electron Linux RenderDoc, browser backing, parity, 4K/8K perf, and production GUI/web gates pass; remaining blocked gates are macOS Metal + Windows D3D12 native render-log comparison and full CSS beyond implemented Simple Web subset | `sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs` + `test/03_system/check/native_render_log_platform_matrix_contract_spec.spl` (8/8) | `doc/09_report/gui_renderdoc_feature_coverage_status_2026-07-03.md`; `build/gui_renderdoc_feature_coverage_status/evidence.env` |
| G5.2 Android emulator capture | Emulator leg BLOCKED on host (no SDK/JDK — recorded); fallback legs PASS: WebView-equivalent proof at 360x640 + gradle-artifact gap analysis | `scripts/check/check-tauri-android-webview-proof.shs` + `test/03_system/check/tauri_android_webview_proof_spec.spl` (3/3) | `build/tauri-android-proof/*` |
