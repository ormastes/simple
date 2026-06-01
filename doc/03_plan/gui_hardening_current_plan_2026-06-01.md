# GUI Hardening Current Plan - 2026-06-01

This is the current single plan/status document for the active GUI hardening
SPipe lane. Use it as the first read for current status, related evidence, and
remaining work. Older plan files remain historical lane notes unless linked
here.

For the real macOS WM implementation path, use
`doc/03_plan/gui_real_implementation_plan_2026-06-01.md`. That plan supersedes
direct-buffer hosted WM demos as release evidence and defines the required
hosted macOS plus AArch64-HVF QEMU stack.

## Objective

Complete the GUI hardening plan with Chrome/corpus work first, then finish the
remaining GUI task lanes: exact bitmap rendering, generated GUI WASM, 8K
color/image handling, vector-font GPU readback, JS/WASM/browser compatibility,
live Electron/QEMU evidence, and release-grade no-tolerance verification.

## Current Status

- Chrome/corpus open gates are green for the bounded offline corpus and current
  exact/no-tolerance harness. The broader production renderer still is not full
  Chrome parity; the known blocker is Chrome-compatible text/font/compositing,
  not corpus generation. The focused `site_0_google` text-line diagnostic now
  uses calibrated pixel-width font metrics, matches Chrome's four-line split,
  and records a first-line width of `105`px versus Chrome canvas `104.0625`px.
  The famous-site corpus system spec passes 37/37; production pixels remain
  divergent (`differentPixels: 2717`) and are tracked as the next glyph paint
  and compositing blocker. Direct bitmap glyph paint routes were probed and
  fail closed because they regress the strict different-pixel bound; the next
  implementation slice needs Chrome-like antialias/proportional glyph paint
  before replacing the rectangle-only production corpus path. The text painter
  now exposes calibrated famous-site paint runs so production paint can consume
  the shared wrapping/width/y-position model without duplicating font metrics.
- 8K color/image Option A is selected and documented: lazy packed 8K surfaces,
  CIELAB as the semantic color space, XYZ as the connection space, and fail-
  closed unsupported codec/profile paths. The JPEG XL stage now distinguishes
  default structured sRGB metadata from non-default structured color headers,
  which fail closed as transform-pending instead of being treated as sRGB.
- Vector-font GPU evidence is expanded beyond the original nine-scene matrix.
  Current evidence proves GPU-returned glyphs with zero CPU fallback for the
  expanded `PIPELINESTATUSOK/24`, `VECTORFONTGPU/36`, and `GPUREADBACKWM/12`
  scenes, plus the broader baseline matrix. The GTK repeat gate now also
  records a fail-closed vector-font-unavailable fallback probe. Metal
  Engine2D framebuffer readback is now explicitly fail-closed on this Linux
  host; current Metal `read_pixels()` evidence remains CPU-mirror-only and does
  not claim a GPU framebuffer download.
- Generated GUI WASM widget-matrix evidence covers source-level and retained
  browser state transitions for dropdowns, dialogs, tables, lists, progress,
  image load/error state, menus, and statusbar state. The widget matrix now
  routes checkbox, dialog, table/list, image/tooltip, scroll, menu, and
  statusbar event responses through shared `common.ui.builder`
  `wasm_widget_state_event_response` helpers instead of local one-off branches.
- Engine2D exact-bitmap coverage now includes split-pane, two-block, wide-card,
  toolbar/modal/grid, dashboard/command/list, form/sidebar/validation,
  settings/inspector/tree, media/gallery/command, report/table/command, and
  image/taskbar/command scenes across Node, Bun, and live Electron captures.
  The consolidated full matrix now passes all ten scenes with zero mismatches
  and no blur/tolerance path.
- Generic Simple Web layout evidence covers colored CSS surfaces, selector and
  inline precedence, descendant scope, and child-scope behavior, but not full
  Chromium DOM/CSS/text parity.
- CommonJS/Node runtime evidence now covers `process.nextTick` scheduling
  through the runtime drain path. The callback path uses the same JS callback
  invoker as promise microtasks, so queued callbacks can mutate runtime globals
  instead of being counted without observable execution.
- HTML compatibility reports now expose exact-pixel policy as structured SDN:
  `exact_required: true`, `perceptual_diagnostic_only: true`, and
  `tolerance_acceptance_allowed: false`. Perceptual percentages remain
  diagnostics only.
- QEMU/GTK evidence has host-side exact GTK scene checks and QMP wiring. The
  live desktop auto-QMP launch reaches `pass`, yields a real QMP socket, and
  strict live QMP screendump capture now passes with zero sample/scene
  mismatches. The same authoritative report now also runs the host GTK GL WM
  exact-scene perf baseline during live-QMP evidence collection, recording
  Simple `1us`, GTK `301us`, `200` iterations, zero RGBA mismatches, and no
  tolerance path. QEMU-side Simple-vs-GTK performance remains unwired.
- Pure GUI release/perf evidence now defines a WM/web/native-runtime-free command
  boundary, SMF/dynlib performance contract, and fail-closed probe row. Current
  Linux-host evidence intentionally reports `pass=false` without a real
  SMF/dynlib artifact, so it does not claim the final native hot-call target.

## Current Evidence

- `doc/09_report/gui_hardening_open_gates_2026-06-01.md`: Chrome/corpus open
  gate report.
- `test/unit/browser_engine/text_painter_spec.spl`: focused
  `site_0_google` text wrapping proof for `Google search`, `deterministic`,
  `compatibility`, and `fixture` line grouping.
- `test/system/wm_compare/famous_site_corpus_spec.spl`: 37/37 passing
  Chrome/corpus system scenarios, including 120px full text-line coverage and
  explicit over-wide 122px/132px mismatch diagnostics.
- `test/baselines/famous_site_corpus/site_0_google/report.production.sdn`:
  focused production artifact with four Simple layout lines and
  `layout_text_match: true`; the first-line width now records `105`px versus
  Chrome `104.0625`px, while pixel output remains divergent for paint/composite
  work.
- `src/app/wm_compare/site_corpus_compat.spl`: production child capture honors
  `SIMPLE_BIN`/`SIMPLE_BINARY` before falling back to `bin/simple`, keeping
  focused probes on the same verified runtime as the parent command instead of
  failing before pixel comparison when the cached wrapper lacks `run` support.
- `test/baselines/famous_site_corpus/site_0_google/report.production.sdn`:
  production text ink evidence now includes per-line regions derived from the
  calibrated Simple paint runs. The four current line deltas are `Google search`
  `808`, `deterministic` `761`, `compatibility` `779`, and `fixture` `368`
  differing pixels, preserving the real `2717` total divergence while making the
  glyph/compositing blocker gateable line by line.
- `doc/09_report/chrome_production_glyph_paint_probe_2026-06-01.md`:
  fail-closed production glyph paint probe showing generic layout and Engine2D
  bitmap glyph routes regress the strict `site_0_google` different-pixel bound.
- `doc/09_report/chrome_text_paint_run_helper_2026-06-01.md`: focused
  text-painter bridge evidence showing calibrated famous-site paint runs for
  the next gated production glyph compositing slice.
- `doc/06_spec/unit/browser_engine/text_painter_spec.md`: generated scenario
  manual for the text painter, including the calibrated paint-run scenario.
- `doc/09_report/gui_color_image_pipeline_8k_current_2026-06-01.md`: current
  packed 8K surface and lazy codec/profile evidence.
- `doc/09_report/gui_color_image_pipeline_8k_evidence_2026-06-01.md`: 8K lane
  canonical evidence with non-identity ICC and JPEG XL non-default structured
  color fail-closed behavior.
- `doc/09_report/vector_font_compute_current_2026-06-01.md`: focused
  vector-font GPU glyph readback evidence.
- `doc/09_report/vector_font_compute_matrix_current_2026-06-01.md`: full
  current vector-font matrix report.
- `doc/09_report/vector_font_compute_matrix_expanded_current_2026-06-01.md`:
  expanded vector-font GPU matrix with `cpu_fallback=0` for all expanded scenes.
- `doc/09_report/metal_engine2d_framebuffer_readback_2026-06-01.md`:
  fail-closed Metal framebuffer readback evidence; Linux reports
  `metal-requires-macos`, `gpu_readback_available=false`, and
  `exact_gpu_claimed=false`.
- `doc/09_report/gtk_gui_repeat_fallback_evidence_2026-06-01.md`: repeat
  open/render evidence with an explicit vector-font unavailable fallback probe.
- `doc/09_report/qemu_gtk_wm_capture_evidence_2026-06-01.md`: live QEMU/GTK
  evidence showing auto-QMP launch reaches `pass` with a socket and strict
  live QMP screendump capture passes with `786432` pixels, `10` sample matches,
  and `0` scene mismatches. The report also records host-side Simple-vs-GTK
  perf baseline fields with Simple `1us`, GTK `301us`, `200` iterations,
  comparison available, `0` RGBA mismatches, and
  `blur_or_tolerance_used=false`.
- `src/lib/common/ui/builder.spl` and
  `examples/ui/widget_matrix_wasm_gui.spl`: shared retained-WASM widget event
  helper and widget-matrix refactor. Current CLI/browser evidence keeps
  widget-matrix import count at `0`, event markers at `23/23`, retained
  selectors at `23/23`, nonzero boxes at `23/23`, and retained event mutations
  at `22/22`.
- `src/app/wm_compare/html_compat_part3.spl`,
  `test/system/wm_compare/html_compat_spec.spl`, and
  `doc/06_spec/system/wm_compare/html_compat_spec.md`: exact-pixel acceptance
  policy is now machine-readable in generated reports with
  `tolerance_acceptance_allowed: false`.
- `src/lib/gui/pure_core.spl`, `src/lib/gui/pure_smf_dynlib_perf.spl`,
  `src/app/gui_perf/smf_dynlib_probe_core.spl`, and
  `src/app/gui_perf/smf_dynlib_probe.spl`: pure GUI command-boundary and
  SMF/dynlib hot-response evidence. The focused CLI row is
  `GUI_DYNLIB_PERF ... call_source=direct_simple ... pass=false
  error=missing-artifact-path`, proving fallback measurements cannot satisfy the
  release gate.
- `src/lib/nogc_sync_mut/js/engine/interpreter_async.spl`,
  `test/feature/js/node_process_next_tick_spec.spl`, and
  `doc/06_spec/feature/js/node_process_next_tick_spec.md`: focused Node
  event-loop evidence proving `process.nextTick` and
  `require('process').nextTick` callbacks run on `drain_due_timers(0)` and
  mutate runtime globals. The focused spec passes `2/2`; the broader
  `node_api_conformance_spec.spl` still has an unrelated residual
  `152 passed / 1 failed` gap.
- `doc/09_report/budgeted_simple_web_engine2d_scene_matrix_settings_inspector_2026-06-01.md`:
  current Engine2D Node/Bun/Electron budgeted exact-bitmap matrix including
  settings-inspector-tree.
- `doc/09_report/budgeted_simple_web_engine2d_scene_matrix_media_gallery_2026-06-01.md`:
  current Engine2D Node/Bun/Electron budgeted exact-bitmap matrix including
  media-gallery-command.
- `doc/09_report/budgeted_simple_web_engine2d_scene_matrix_report_table_2026-06-01.md`:
  current Engine2D Node/Bun/Electron budgeted exact-bitmap matrix including
  report-table-command.
- `doc/09_report/budgeted_simple_web_engine2d_scene_matrix_full_2026-06-01.md`:
  consolidated Engine2D Node/Bun/Electron budgeted exact-bitmap matrix for all
  ten current scenes, including `image-taskbar-command`, with every runtime
  passing at zero mismatches and no blur/tolerance path.
- `doc/09_report/node_simple_web_engine2d_image_taskbar_command_bitmap_evidence_2026-06-01.md`,
  `doc/09_report/bun_simple_web_engine2d_image_taskbar_command_bitmap_evidence_2026-06-01.md`,
  and `doc/09_report/electron_simple_web_engine2d_image_taskbar_command_bitmap_evidence_2026-06-01.md`:
  current image-taskbar-command exact-bitmap evidence across Node, Bun, and
  live Electron, all with zero mismatches and no blur/tolerance path.
- `doc/09_report/gui_wasm_browser_execution_widget_state_machine_debug_2026-06-01.md`:
  generated GUI WASM retained-browser state-machine evidence.
- `doc/09_report/gui_wasm_cli_artifact_widget_state_machine_debug_2026-06-01.md`,
  `doc/09_report/gui_wasm_target_package_widget_state_machine_debug_2026-06-01.md`,
  and `doc/09_report/gui_wasm_host_wm_launch_widget_state_machine_debug_2026-06-01.md`:
  generated GUI WASM artifact, package, and host-WM launch evidence.

## Related Docs

- `doc/03_plan/simple_web_renderer_chrome_compat_corpus.md`: Chrome/corpus
  corpus, fixture, production-renderer contrast, and remaining text parity
  details.
- `doc/03_plan/simple_web_renderer_completion_audit.md`: historical Simple Web
  renderer completion audit and Chrome parity blocker analysis.
- `doc/03_plan/gui_renderer_restart_plan_2026-05-29.md`: restart-era platform
  and renderer lane evidence.
- `doc/02_requirements/feature/gui_color_image_pipeline_8k.md` and
  `doc/02_requirements/nfr/gui_color_image_pipeline_8k.md`: selected 8K Option
  A requirements.
- `doc/04_architecture/gui_color_image_pipeline_8k.md` and
  `doc/05_design/gui_color_image_pipeline_8k.md`: 8K architecture and detail
  design.

## Remaining Work

- Production Chrome parity: replace fixture/oracle-backed corpus shortcuts with
  real Chrome-compatible DOM/style/layout/font paint output. The current
  production probe remains divergent for text-heavy corpus samples; the next
  slice should implement Chrome-like antialias/proportional glyph paint and
  compositing before moving the matched line metrics into production paint. Do
  not replace the current rectangle-only production corpus path with binary
  bitmap glyph text; the fail-closed probe shows that regresses the strict
  different-pixel bound.
- 8K color/image: broaden high-bit-depth compressed raster coverage, JPEG XL
  codestream pixel decoding, real non-identity ICC/profile transforms, broader
  JPEG XL structured/ICC color parser coverage, and web/browser/WM image
  integration.
- Vector-font GPU: turn current evidence-kernel glyph return into reusable
  production buffer ownership/readback across arbitrary text runs, more font
  sizes, and broader kernel parameter combinations. Add the Apple-host native
  compiled Metal proof that downloads the GPU framebuffer and compares it to the
  CPU mirror for `clear`, `rect_filled`, and one vector-text scene before
  claiming Engine2D/Metal framebuffer readback parity.
- Engine2D/Simple Web exact bitmap: keep expanding Node/Bun/Electron scene
  coverage into broader HTML/CSS/image/text/taskbar/command-bar scenes and
  deeper layout/style features before claiming text-flow parity.
- JS/WebEngine/WASM: go beyond bounded metadata, typed-array, `DataView`, and
  callable-stub paths into broader instruction execution, traps, table/global
  exports, import binding, async instantiate semantics, and fuller typed-array
  prototype behavior.
- CommonJS/Node APIs: extend beyond builtin module cache, deterministic
  `process.exit`, `path`, `Buffer`, and bounded process metadata to real module
  execution/cache semantics, package resolution, timers/event loop, streams,
  networking, and sandboxed `fs` capability design.
- Generated GUI WASM: move widget-matrix-specific state patterns into shared
  per-widget state helpers and cover additional generated apps.
- Live Electron: maintain the passing ten-scene Node/Bun/Electron exact-bitmap
  matrix and extend it into deeper HTML/CSS/image/text/taskbar scenes while
  keeping Chromium DOM/CSS bit-parity claims blocked until font/layout
  divergence is solved.
- QEMU/GTK: add a guest-side GTK/Simple performance harness and broaden strict
  live QEMU WM capture to representative app windows, text glyph content, and
  event-driven retained rendering. Host-side exact GTK scene perf is now wired
  into the live-QMP report, but it is not a substitute for the guest-side
  harness.
- Tolerance audit: continue removing or quarantining legacy perceptual/tolerance
  claims outside the audited GUI hardening paths. Exact pixels remain the
  acceptance rule; perceptual values are diagnostic only.

## Latest Local Verification

- `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl test/unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.spl`
- `SIMPLE_LIB=src bin/simple test test/unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.spl --mode=interpreter --clean --format json`
- `sh scripts/check-node-simple-web-engine2d-settings-inspector-tree-bitmap-evidence.shs`
- `sh scripts/check-bun-simple-web-engine2d-settings-inspector-tree-bitmap-evidence.shs`
- `sh scripts/check-electron-simple-web-engine2d-settings-inspector-tree-bitmap-evidence.shs`
- `sh scripts/check-node-simple-web-engine2d-media-gallery-command-bitmap-evidence.shs`
- `sh scripts/check-bun-simple-web-engine2d-media-gallery-command-bitmap-evidence.shs`
- `sh scripts/check-electron-simple-web-engine2d-media-gallery-command-bitmap-evidence.shs`
- `NODE_BITMAP_ITERATIONS=20 sh scripts/check-node-simple-web-engine2d-report-table-command-bitmap-evidence.shs`
- `NODE_BITMAP_ITERATIONS=20 sh scripts/check-bun-simple-web-engine2d-report-table-command-bitmap-evidence.shs`
- `ELECTRON_BITMAP_ITERATIONS=1 sh scripts/check-electron-simple-web-engine2d-report-table-command-bitmap-evidence.shs`
- `BUDGETED_MATRIX_BITMAP_ITERATIONS=20 BUDGETED_MATRIX_BITMAP_TRIALS=1 BUDGETED_MATRIX_ELECTRON_ITERATIONS=1 BUILD_DIR=build/budgeted_simple_web_engine2d_scene_matrix_settings_inspector REPORT_PATH=doc/09_report/budgeted_simple_web_engine2d_scene_matrix_settings_inspector_2026-06-01.md sh scripts/check-budgeted-simple-web-engine2d-scene-matrix-bitmap-evidence.shs`
- `BUDGETED_MATRIX_BITMAP_ITERATIONS=20 BUDGETED_MATRIX_BITMAP_TRIALS=1 BUDGETED_MATRIX_ELECTRON_ITERATIONS=1 BUILD_DIR=build/budgeted_simple_web_engine2d_scene_matrix_media_gallery REPORT_PATH=doc/09_report/budgeted_simple_web_engine2d_scene_matrix_media_gallery_2026-06-01.md sh scripts/check-budgeted-simple-web-engine2d-scene-matrix-bitmap-evidence.shs`
- `BUDGETED_MATRIX_BITMAP_ITERATIONS=20 BUDGETED_MATRIX_BITMAP_TRIALS=1 BUDGETED_MATRIX_ELECTRON_ITERATIONS=1 BUILD_DIR=build/budgeted_simple_web_engine2d_scene_matrix_report_table REPORT_PATH=doc/09_report/budgeted_simple_web_engine2d_scene_matrix_report_table_2026-06-01.md sh scripts/check-budgeted-simple-web-engine2d-scene-matrix-bitmap-evidence.shs`
- `SIMPLE_BIN=src/compiler_rust/target/release/simple sh scripts/check-node-simple-web-engine2d-image-taskbar-command-bitmap-evidence.shs`
- `SIMPLE_BIN=src/compiler_rust/target/release/simple sh scripts/check-bun-simple-web-engine2d-image-taskbar-command-bitmap-evidence.shs`
- `SIMPLE_BIN=src/compiler_rust/target/release/simple sh scripts/check-electron-simple-web-engine2d-image-taskbar-command-bitmap-evidence.shs`
- `SIMPLE_BIN=src/compiler_rust/target/release/simple BUDGETED_MATRIX_BITMAP_ITERATIONS=20 BUDGETED_MATRIX_BITMAP_TRIALS=1 BUDGETED_MATRIX_ELECTRON_ITERATIONS=1 BUILD_DIR=build/budgeted_simple_web_engine2d_scene_matrix_full REPORT_PATH=doc/09_report/budgeted_simple_web_engine2d_scene_matrix_full_2026-06-01.md sh scripts/check-budgeted-simple-web-engine2d-scene-matrix-bitmap-evidence.shs`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/gc_async_mut/gpu/browser_engine/text_painter.spl test/unit/browser_engine/text_painter_spec.spl`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/unit/browser_engine/text_painter_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src bin/simple check src/app/wm_compare/site_corpus_layout_report.spl test/system/wm_compare/famous_site_corpus_spec.spl test/unit/browser_engine/text_painter_spec.spl`
- `SIMPLE_LIB=src bin/simple test test/unit/browser_engine/text_painter_spec.spl --mode=interpreter --clean --format json`
- `node tools/electron-shell/verify_famous_site_production_probe.js --sample=site_0_google`
- `SIMPLE_LIB=src bin/simple test test/system/wm_compare/famous_site_corpus_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`

All commands above passed in the current worktree.

Additional continuation check:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/wm_compare/site_corpus_compat.spl test/system/wm_compare/famous_site_corpus_spec.spl test/unit/browser_engine/text_painter_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple run src/app/wm_compare/site_corpus_compat.spl --only=site_0_google --production-renderer --continue-on-fail --simple-timeout-ms=60000`

The continuation check passed compilation and restored the focused production
probe to the real `site_0_google` text/compositing blocker: child capture
succeeds, `different_pixels` is `2717`, `layout_text_match` is `true`, and the
report retains the exact-pixel acceptance policy with perceptual values as
diagnostics only.

Per-line text ink continuation check:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/wm_compare/site_corpus_compat.spl test/system/wm_compare/famous_site_corpus_spec.spl test/unit/browser_engine/text_painter_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple run src/app/wm_compare/site_corpus_compat.spl --only=site_0_google --production-renderer --continue-on-fail --simple-timeout-ms=60000`
- `node tools/electron-shell/verify_famous_site_production_probe.js --sample=site_0_google`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/wm_compare/famous_site_corpus_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/system/wm_compare/famous_site_corpus_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The per-line gate passed with `hasTextLineInkDelta: true`,
`textLineInkDeltaCount: 4`, `differentPixels: 2717`, no verifier failures, and
the system spec passing `37/37`. The doc layout guard returned `0`.

Generated GUI WASM shared-helper continuation check:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/common/ui/builder.spl examples/ui/widget_matrix_wasm_gui.spl test/unit/app/ui/builder_spec.spl`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple examples/ui/widget_matrix_wasm_gui.spl`
- `SIMPLE_BIN=src/compiler_rust/target/release/simple sh scripts/check-gui-wasm-cli-artifact.shs`
- `SIMPLE_BIN=src/compiler_rust/target/release/simple sh scripts/check-gui-wasm-browser-execution-evidence.shs`

The compile and generated-WASM gates passed. The source run returned
`wasm_gui:event:matrix_checkbox:changed`; CLI artifact evidence passed with
widget-matrix byte size `15028` and import count `0`; browser evidence passed
with widget-matrix `simple_app_event_probe=23`, event markers `23/23`, retained
selectors `23/23`, nonzero boxes `23/23`, and retained event mutations `22/22`.
`test/unit/app/ui/builder_spec.spl` still has an unrelated focused unit gap at
`43 passed / 2 failed`, so it is not used as release evidence for this slice.

Tolerance-audit continuation check:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/wm_compare/html_compat_part1.spl src/app/wm_compare/html_compat_part3.spl test/system/wm_compare/html_compat_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/wm_compare/html_compat_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/system/wm_compare/html_compat_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The focused html-compat check passed, the system spec passed `17/17`, the
generated manual includes the structured exact-pixel policy assertion, and the
doc layout guard returned `0`.

Pure GUI release/perf continuation check:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/gui/pure_core.spl src/lib/gui/pure_smf_dynlib_perf.spl src/app/gui_perf/smf_dynlib_probe_core.spl src/app/gui_perf/smf_dynlib_probe.spl test/unit/lib/gui/pure_core_spec.spl test/unit/lib/gui/pure_smf_dynlib_perf_spec.spl test/unit/lib/gui/pure_gui_release_lane_spec.spl test/unit/app/gui_perf/smf_dynlib_probe_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/gui/pure_core_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/gui/pure_smf_dynlib_perf_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/gui/pure_gui_release_lane_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/app/gui_perf/smf_dynlib_probe_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple run src/app/gui_perf/smf_dynlib_probe.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/gui/pure_core_spec.spl test/unit/lib/gui/pure_smf_dynlib_perf_spec.spl test/unit/lib/gui/pure_gui_release_lane_spec.spl test/unit/app/gui_perf/smf_dynlib_probe_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The focused check passed; specs passed `6/6`, `7/7`, `7/7`, and `4/4`.
The probe emitted a machine-readable fail-closed row with `pass=false` and
`error=missing-artifact-path` because no real SMF/dynlib artifact was provided.
The generated manuals exist under `doc/06_spec/unit/...`, and the doc layout
guard returned `0`.

Structural layout diagnostics continuation check:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/wm_compare/site_corpus_layout_report.spl src/app/wm_compare/structural_layout_report.spl test/system/wm_compare/structural_layout_report_spec.spl test/system/wm_compare/famous_site_corpus_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/wm_compare/structural_layout_report_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/wm_compare/famous_site_corpus_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/system/wm_compare/structural_layout_report_spec.spl`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The structural diagnostics check passed compilation, the focused structural spec
passed `5/5`, and the famous-site corpus spec passed `37/37` with the new
structural report assertions. `doc/06_spec/system/wm_compare/structural_layout_report_spec.md`
is maintained manually for this slice because `spipe-docgen` is currently
blocked by the unrelated `unknown extern function: shell` semantic error. The
doc layout guard returned `0`.

Shared TUI/GUI structural and WM text-access continuation check:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/wm_compare/structural_layout_report.spl src/app/wm_compare/site_corpus_layout_report.spl src/lib/common/ui/win_text_access.spl test/system/wm_compare/structural_layout_report_spec.spl test/system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/wm_compare/structural_layout_report_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The shared structural and WM text-access check passed compilation. The focused
structural layout report spec passed `5/5`, the WM text-access MCP spec passed
`10/10`, and the doc layout guard returned `0`. The placeholder scan over the
touched executable artifacts found no live placeholder pass markers; matches
were limited to historical state/plan prose.

Backend-qualified measurement continuation check:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/wm_compare/backend_measurement_report.spl test/system/wm_compare/backend_measurement_report_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/wm_compare/backend_measurement_report_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/system/wm_compare/backend_measurement_report_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The backend measurement source/spec check passed and the executable spec passed
`5/5`, proving the selected NFR C record contract for initialized accelerated
lanes, explicit unavailable reasons, fallback rejection, and the Metal/Vulkan/
CUDA/CPU SIMD matrix. The mirrored scenario manual already documents the same
contract. `spipe-docgen` remains blocked by the unrelated
`unknown extern function: shell` semantic error, and the doc layout guard
returned `0`.

GitHub sync checkpoint and backend measurement capture continuation:

- `jj git fetch`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/wm_compare/backend_measurement_capture.spl src/app/wm_compare/backend_measurement_report.spl test/system/wm_compare/backend_measurement_capture_spec.spl test/system/wm_compare/backend_measurement_report_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/wm_compare/backend_measurement_capture_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/wm_compare/backend_measurement_report_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The GitHub fetch checkpoint reported `Nothing changed`; no rebase or push was
attempted because the repository is still detached with dirty jj working-copy
changes. Backend measurement capture/report typechecked together, the capture
spec passed `3/3`, the report spec passed `5/5`, the capture manual lists 3
active scenarios, and the doc layout guard returned `0`.

SMF/dynlib release-lane continuation check:

- `jj git fetch`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/gui_perf/smf_dynlib_artifact.spl src/app/gui_perf/smf_wrap_host_dynlib.spl src/app/gui_perf/smf_dynlib_probe_core.spl test/unit/app/gui_perf/smf_dynlib_artifact_spec.spl test/unit/app/gui_perf/smf_dynlib_probe_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/app/gui_perf/smf_dynlib_artifact_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/app/gui_perf/smf_dynlib_probe_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The GitHub fetch checkpoint again reported `Nothing changed`. The SMF/dynlib
artifact and probe files typechecked, `smf_dynlib_artifact_spec` passed `3/3`,
and `smf_dynlib_probe_spec` passed `9/9`. The mirrored manuals exist under
`doc/06_spec/unit/app/gui_perf/`. The host dynlib evidence report proves the
pure GUI hot symbol is callable through a real host dynlib at `p50_us=17` and
`p95_us=19`, while still rejecting that sample as `not-smf-dynlib`; this keeps
SMF acceptance separate from host-dynlib diagnostics. Placeholder scan matches
were legitimate SMF `stub` terminology, not placeholder pass markers. The doc
layout guard returned `0`.

Production Chrome parity refresh:

- `jj git fetch`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple run src/app/wm_compare/site_corpus_compat.spl --only=site_0_google --production-renderer --continue-on-fail --simple-timeout-ms=60000`
- `node tools/electron-shell/verify_famous_site_production_probe.js --sample=site_0_google`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/wm_compare/site_corpus_compat.spl test/system/wm_compare/famous_site_corpus_spec.spl tools/electron-shell/verify_famous_site_production_probe.js`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/wm_compare/famous_site_corpus_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The GitHub fetch checkpoint reported `Nothing changed`. The focused production
report was regenerated and the verifier passed with `differentPixels=2717`,
`computedDifferentPixels=2717`, `reportFresh=true`, `layoutTextMatch=true`,
`hasTextLineInkDelta=true`, and `textLineInkDeltaCount=4`. The famous-site
system spec passed `37/37`, and the doc layout guard returned `0`. This is
current evidence for the Chrome text/font/compositing blocker; the blocker
remains open because the production renderer is still divergent rather than
Chrome-exact.
