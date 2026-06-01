# GUI Hardening Current Plan - 2026-06-01

This is the current single plan/status document for the active GUI hardening
SPipe lane. Use it as the first read for current status, related evidence, and
remaining work. Older plan files remain historical lane notes unless linked
here.

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
  uses calibrated pixel-width font metrics and matches Chrome's four-line split.
  The famous-site corpus system spec passes 37/37; production pixels remain
  divergent (`differentPixels: 2717`) and are tracked as the next glyph paint
  and compositing blocker.
- 8K color/image Option A is selected and documented: lazy packed 8K surfaces,
  CIELAB as the semantic color space, XYZ as the connection space, and fail-
  closed unsupported codec/profile paths.
- Vector-font GPU evidence is expanded beyond the original nine-scene matrix.
  Current evidence proves GPU-returned glyphs with zero CPU fallback for the
  expanded `PIPELINESTATUSOK/24`, `VECTORFONTGPU/36`, and `GPUREADBACKWM/12`
  scenes, plus the broader baseline matrix. The GTK repeat gate now also
  records a fail-closed vector-font-unavailable fallback probe.
- Generated GUI WASM widget-matrix evidence covers source-level and retained
  browser state transitions for dropdowns, dialogs, tables, lists, progress,
  image load/error state, menus, and statusbar state.
- Engine2D exact-bitmap coverage now includes split-pane, two-block, wide-card,
  toolbar/modal/grid, dashboard/command/list, form/sidebar/validation,
  settings/inspector/tree, media/gallery/command, and image/taskbar/command
  scenes across Node, Bun, and live Electron captures.
- Generic Simple Web layout evidence covers colored CSS surfaces, selector and
  inline precedence, descendant scope, and child-scope behavior, but not full
  Chromium DOM/CSS/text parity.
- QEMU/GTK evidence has host-side exact GTK scene checks and QMP wiring, but
  QEMU-side Simple-vs-GTK performance remains unwired. Live QEMU desktop auto
  launch currently fails closed before readiness.

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
  `layout_text_match: true`; pixel output remains divergent for paint/composite
  work.
- `doc/09_report/gui_color_image_pipeline_8k_current_2026-06-01.md`: current
  packed 8K surface and lazy codec/profile evidence.
- `doc/09_report/gui_color_image_pipeline_8k_evidence_2026-06-01.md`: 8K lane
  canonical evidence with non-identity ICC fail-closed behavior.
- `doc/09_report/vector_font_compute_current_2026-06-01.md`: focused
  vector-font GPU glyph readback evidence.
- `doc/09_report/vector_font_compute_matrix_current_2026-06-01.md`: full
  current vector-font matrix report.
- `doc/09_report/vector_font_compute_matrix_expanded_current_2026-06-01.md`:
  expanded vector-font GPU matrix with `cpu_fallback=0` for all expanded scenes.
- `doc/09_report/gtk_gui_repeat_fallback_evidence_2026-06-01.md`: repeat
  open/render evidence with an explicit vector-font unavailable fallback probe.
- `doc/09_report/budgeted_simple_web_engine2d_scene_matrix_settings_inspector_2026-06-01.md`:
  current Engine2D Node/Bun/Electron budgeted exact-bitmap matrix including
  settings-inspector-tree.
- `doc/09_report/budgeted_simple_web_engine2d_scene_matrix_media_gallery_2026-06-01.md`:
  current Engine2D Node/Bun/Electron budgeted exact-bitmap matrix including
  media-gallery-command.
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
  slice should move the matched line metrics into production glyph paint and
  compositing rather than adding more corpus fixture shortcuts.
- 8K color/image: broaden high-bit-depth compressed raster coverage, JPEG XL
  codestream color parsing and pixel decoding, real non-identity ICC/profile
  transforms, and web/browser/WM image integration.
- Vector-font GPU: turn current evidence-kernel glyph return into reusable
  production buffer ownership/readback across arbitrary text runs, more font
  sizes, and broader kernel parameter combinations.
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
- Live Electron: extend exact live capture to the broader Node/Bun scene matrix
  while keeping Chromium DOM/CSS bit-parity claims blocked until font/layout
  divergence is solved.
- QEMU/GTK: add a guest-side GTK/Simple performance harness and broaden strict
  live QEMU WM capture to representative app windows, text glyph content, and
  event-driven retained rendering.
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
- `BUDGETED_MATRIX_BITMAP_ITERATIONS=20 BUDGETED_MATRIX_BITMAP_TRIALS=1 BUDGETED_MATRIX_ELECTRON_ITERATIONS=1 BUILD_DIR=build/budgeted_simple_web_engine2d_scene_matrix_settings_inspector REPORT_PATH=doc/09_report/budgeted_simple_web_engine2d_scene_matrix_settings_inspector_2026-06-01.md sh scripts/check-budgeted-simple-web-engine2d-scene-matrix-bitmap-evidence.shs`
- `BUDGETED_MATRIX_BITMAP_ITERATIONS=20 BUDGETED_MATRIX_BITMAP_TRIALS=1 BUDGETED_MATRIX_ELECTRON_ITERATIONS=1 BUILD_DIR=build/budgeted_simple_web_engine2d_scene_matrix_media_gallery REPORT_PATH=doc/09_report/budgeted_simple_web_engine2d_scene_matrix_media_gallery_2026-06-01.md sh scripts/check-budgeted-simple-web-engine2d-scene-matrix-bitmap-evidence.shs`
- `SIMPLE_LIB=src bin/simple check src/app/wm_compare/site_corpus_layout_report.spl test/system/wm_compare/famous_site_corpus_spec.spl test/unit/browser_engine/text_painter_spec.spl`
- `SIMPLE_LIB=src bin/simple test test/unit/browser_engine/text_painter_spec.spl --mode=interpreter --clean --format json`
- `node tools/electron-shell/verify_famous_site_production_probe.js --sample=site_0_google`
- `SIMPLE_LIB=src bin/simple test test/system/wm_compare/famous_site_corpus_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`

All commands above passed in the current worktree.
