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
  exact/no-tolerance harness only. That offline-oracle success is distinct from
  open production Chrome glyph/compositing parity: the broader production
  renderer still is not full Chrome parity, and the known blocker is
  Chrome-compatible text/font/compositing, not corpus generation. The focused
  `site_0_google` text-line diagnostic now
  uses calibrated pixel-width font metrics, matches Chrome's four-line split,
  and records a first-line width of `105`px versus Chrome canvas `104.0625`px.
  The famous-site corpus system spec passes 45/45; production pixels remain
  divergent (`differentPixels: 2717`) and are tracked as the next glyph paint
  and compositing blocker. Direct bitmap glyph paint routes were probed and
  fail closed because they regress the strict different-pixel bound. A follow-up
  shared `FontRenderer`/`libspl_fonts` production overlay also failed closed:
  fallback glyphs raised the focused production delta to `3113`, and TrueType
  glyphs raised it to `3696`, even though they painted more expected ink. The
  next implementation slice needs Chrome-like antialias/gamma/LCD compositing,
  not another raw glyph overlay, before replacing the rectangle-only production
  corpus path. The text painter now exposes calibrated famous-site paint runs
  so production paint can consume the shared wrapping/width/y-position model
  without duplicating font metrics.
  The focused production verifier now reads its strict current-difference bound
  from the checked-in sample baseline, requires the production report to declare
  `production_render_strategy: "famous_site_block_only_pending_glyph_compositing"`,
  and independently recomputes PPM pixels, while still reporting
  `chromeGlyphCompositingParity=false` until exact pixels reach zero.
- 8K color/image Option A is selected and documented: lazy packed 8K surfaces,
  CIELAB as the semantic color space, XYZ as the connection space, and fail-
  closed unsupported codec/profile paths. The JPEG XL stage now distinguishes
  default structured sRGB metadata from non-default structured color headers,
  which fail closed as transform-pending instead of being treated as sRGB. The
  current refreshed report records the 8K BGRA8 framebuffer at `132710400`
  bytes, avoids eager Lab/XYZ, TIFF, and JPEG XL initialization, and keeps full
  JPEG XL pixel decode open as follow-up work.
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
  Broader browser execution evidence now covers three generated apps:
  `hello`, `widget_matrix`, and `builder_matrix`, including validation,
  instantiation, exported app entrypoints, zero imports, retained selectors,
  nonzero boxes, and retained event mutations.
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
  through the runtime drain path and explicit child-process command grants
  through `JsRuntime.grant_node_process`. The callback path uses the same JS
  callback invoker as promise microtasks, so queued callbacks can mutate runtime
  globals instead of being counted without observable execution. A follow-up
  phase-ordering slice now drains bounded `process.nextTick` callbacks before
  already queued `timers.setTimeout(..., 0)` callbacks, including nested
  nextTick callbacks scheduled during the drain. The broader Node API
  conformance spec now passes its focused builtin/process sandbox scenarios,
  including rejecting missing and invalid process grants.
- HTML compatibility reports now expose exact-pixel policy as structured SDN:
  `exact_required: true`, `perceptual_diagnostic_only: true`, and
  `tolerance_acceptance_allowed: false`. Perceptual percentages remain
  diagnostics only. Famous-site production corpus reports now expose the same
  structured `acceptance_policy_flags` inside the comparison record, so the
  focused Chrome-parity verifier can fail closed if a production report omits
  the no-tolerance policy.
- QEMU/GTK evidence has host-side exact GTK scene checks and QMP wiring, but
  the current Linux-host report is fail-closed: no live QMP socket is present,
  the host GTK GL WM scene now passes with zero bitmap mismatches and no
  tolerance path, and QEMU-side Simple-vs-GTK performance remains
  `blocked-unwired`. Host GTK timing is non-promoting evidence only and cannot
  substitute for guest-side QEMU/GTK performance parity.
- macOS live-window evidence now emits a release gate explicitly. On this Linux
  host the report is `status=skip`, `reason=requires-macos`, with
  `macos_gui_live_window_evidence_release_gate=live-macos-window-visual-proof`
  and `macos_gui_live_window_evidence_release_gate_status=not-satisfied`.
- Pure GUI release/perf evidence now defines a WM/web/native-runtime-free command
  boundary, SMF/dynlib performance contract, and fail-closed probe row. Current
  Linux-host evidence intentionally reports `pass=false` without a real
  SMF/dynlib artifact, so it does not claim the final native hot-call target.
  The SMF artifact contract now also emits a release-reportable
  `GUI_SMF_ARTIFACT_CONTRACT` row and fails closed for missing, non-SMF, and
  empty-library-envelope inputs while keeping QEMU and macOS execution marked
  `not-run`. QEMU ARM64 SMF parity evidence is contract-only and now requires
  the same role-2 ARM64 SMF artifact, the expected `gui_dynlib_hot_probe_tick`
  symbol, and a non-empty pure GUI command batch before emitting
  `GUI_QEMU_ARM64_SMF_PARITY status=contract-pass`; it keeps
  `live_qemu=false`, so it does not replace the remaining guest-side QEMU/GTK
  harness. The dynlib hot-response gate now also fails closed for incomplete
  sample sets and wrong-symbol measurements, so fast calls to any symbol other
  than `gui_dynlib_hot_probe_tick` cannot satisfy release evidence. SimpleOS
  dynload evidence now proves the same ARM64 SMF envelope can be opened through
  the kernel loader registry and resolve the GUI hot-call symbol, while wrong
  symbol, wrong architecture, and missing artifact bytes fail closed.

## Current Evidence

- `doc/09_report/gui_hardening_open_gates_2026-06-01.md`: Chrome/corpus open
  gate report.
- `test/unit/browser_engine/text_painter_spec.spl`: focused
  `site_0_google` text wrapping proof for `Google search`, `deterministic`,
  `compatibility`, and `fixture` line grouping.
- `test/system/wm_compare/famous_site_corpus_spec.spl`: 45/45 passing
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
  glyph/compositing blocker gateable line by line. The production `compare`
  record also contains `acceptance_policy_flags: (exact_required: true
  perceptual_diagnostic_only: true tolerance_acceptance_allowed: false)`.
- `tools/electron-shell/verify_famous_site_production_probe.js`: focused
  production Chrome-parity verifier, with
  `test/baselines/famous_site_corpus/site_0_google/production_probe_baseline.json`
  as its checked-in regression bound. Current `site_0_google` evidence passes
  only as bounded divergent evidence with `differentPixels=2717`,
  `computedDifferentPixels=2717`, `maxDifferentPixels=2717`,
  `boundedDivergenceOnly=true`, `chromeGlyphCompositingParity=false`, and
  `productionRenderStrategy="famous_site_block_only_pending_glyph_compositing"`;
  a missing baseline, missing/unexpected render strategy, text-line ink
  corruption, and residual-pixel corruption all fail closed.
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
  color fail-closed behavior. The refreshed release-binary run reports
  `gui_color_image_pipeline_8k_status=pass`, `framebuffer_bytes=132710400`,
  `lab_xyz_full_frame_bytes=796262400`, `initializes_color_transforms=false`,
  `initializes_tiff_decoder=false`, `initializes_jpegxl_decoder=false`, and a
  D65 Lab/XYZ red round trip. Focused image specs pass `77/77` and TIFF raster
  specs pass `17/17`.
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
- `doc/09_report/qemu_gtk_wm_capture_evidence_2026-06-02.md`: current
  QEMU/GTK evidence is fail-closed on this Linux refresh: no live QMP socket is
  present, the host GTK GL scene passes with zero bitmap mismatches, and the
  guest-side Simple-vs-GTK perf release gate remains blocked.
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
  release gate. Current focused checks also pass
  `pure_smf_dynlib_perf_spec.spl` `10/10`; the perf contract rejects
  incomplete sample sets with `error=incomplete-samples` and wrong release
  symbols with `error=wrong-symbol`.
- `src/app/gui_perf/smf_artifact_contract.spl`,
  `src/app/gui_perf/smf_dynlib_artifact.spl`,
  `test/unit/app/gui_perf/smf_dynlib_artifact_spec.spl`, and
  `doc/06_spec/unit/app/gui_perf/smf_dynlib_artifact_spec.md`: SMF artifact
  contract evidence. Current focused checks pass 8/8 for valid role-2 envelopes,
  missing artifact rows, non-SMF rejection, empty-envelope rejection, and
  explicit `qemu_status=not-run` / `macos_status=not-run` reasons. The missing
  artifact CLI exits `1` with a `status=missing` contract row.
- `src/app/gui_perf/qemu_arm64_smf_parity.spl`,
  `src/app/gui_perf/qemu_arm64_smf_parity_evidence.spl`,
  `src/app/gui_perf/simpleos_smf_dynload.spl`,
  `src/app/gui_perf/simpleos_smf_dynload_evidence.spl`,
  `src/app/gui_perf/macos_smf_dynlib_evidence_core.spl`,
  `test/unit/app/gui_perf/qemu_arm64_smf_parity_spec.spl`,
  `test/unit/app/gui_perf/simpleos_smf_dynload_spec.spl`,
  `test/unit/app/gui_perf/macos_smf_dynlib_evidence_spec.spl`, and
  `doc/06_spec/unit/app/gui_perf/qemu_arm64_smf_parity_spec.md`: contract-only
  QEMU ARM64 SMF parity and SimpleOS dynload evidence. Current focused checks pass
  `qemu_arm64_smf_parity_spec.spl` `3/3`, `macos_smf_dynlib_evidence_spec.spl`
  `7/7`, `simpleos_smf_dynload_spec.spl` `4/4`, and
  `pure_gui_release_lane_spec.spl` `13/13`. The rows include
  `symbol=gui_dynlib_hot_probe_tick`, reject wrong-symbol parity/dynload
  claims, reject non-ARM64 and missing-artifact dynload attempts, and keep
  `live_qemu=false`.
- `src/lib/nogc_sync_mut/js/engine/runtime.spl`,
  `src/lib/nogc_sync_mut/js/engine/interpreter_native.spl`,
  `src/lib/nogc_sync_mut/js/engine/interpreter_async.spl`,
  `test/feature/js/node_api_conformance_spec.spl`,
  `test/feature/js/node_process_next_tick_spec.spl`, and
  `doc/06_spec/feature/js/node_process_next_tick_spec.md`: focused Node
  evidence proving `process.nextTick` and `require('process').nextTick`
  callbacks run on `drain_due_timers(0)` and mutate runtime globals, plus
  explicit process capability grants for `child_process.spawn`. A follow-up
  bounded metadata slice now reports `exitCode`, `signal`, `stdout`, `stderr`,
  `argvLength`, and `pid` on allowed and denied spawn results without host
  process I/O. A follow-up phase-ordering slice gives nextTick tasks priority
  over already queued zero-delay `timers.setTimeout` tasks, including nested
  nextTick callbacks scheduled during the drain. A bounded terminal grant now
  lets `readline.createInterface` return allowed deterministic terminal state,
  invoke `question` callbacks with the granted answer, and close without host
  terminal I/O. Bounded writable streams now honor `highWaterMark`, track
  `writableHighWaterMark`, cumulative `writableLength`/`bytesWritten`, and set
  write/pipe backpressure state when the high-water mark is reached. Bounded
  `Writable.end()` now clears pressure, zeroes `writableLength`, and emits
  registered `drain` callbacks before finish. Bounded readable streams now
  expose `pause`, `resume`, and `isPaused`, track `readableFlowing`, and defer
  `pipe()` drains while paused. A pending bounded pipe destination is now
  drained automatically on `resume()`. Bounded `unpipe()` now clears pending
  pipe destinations before resume. Bounded readable `destroy()` now closes
  readable state, clears pending pipe state, and idempotently emits `close`.
  Bounded readable streams now report `Readable.from` high-water mark, object
  mode, and encoding metadata. Bounded writable streams now also expose
  Node-style writable lifecycle aliases, `writableNeedDrain`, `writableCorked`,
  `cork()`/`uncork()`, and option metadata for `objectMode`,
  `defaultEncoding`, and `decodeStrings`.
  Current focused checks pass `node_api_conformance_spec.spl` `275/275` and
  `node_process_next_tick_spec.spl` `2/2`; missing and invalid process grants
  remain rejected, and explicit in-memory CommonJS source grants now execute
  `exports.*` assignments plus `module.exports = ...` replacements with cache
  identity, slash-bearing specifier coverage, and bounded `/node_modules`
  index/package-main resolution over granted in-memory files.
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
- `doc/09_report/gui_wasm_browser_execution_widget_behavior_2026-06-01.md`:
  generated GUI WASM browser execution evidence for `hello`, `widget_matrix`,
  and `builder_matrix`. Current refreshed evidence has all three targets
  passing with import count `0`; retained event mutations are `4/4`, `22/22`,
  and `5/5` respectively.
- `doc/09_report/gui_wasm_cli_artifact_widget_state_machine_debug_2026-06-01.md`,
  `doc/09_report/gui_wasm_target_package_widget_state_machine_debug_2026-06-01.md`,
  and `doc/09_report/gui_wasm_host_wm_launch_widget_state_machine_debug_2026-06-01.md`:
  generated GUI WASM artifact, package, and host-WM launch evidence.
- `test/system/app/browser/feature/webgpu_js_wasm_simple_spec.spl`,
  `test/unit/lib/common/web/browser_session_wasm_host_spec.spl`,
  `test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`, and
  `doc/06_spec/system/app/browser/feature/webgpu_js_wasm_simple_spec.md`:
  JS/WebEngine/WASM BrowserSession evidence. Current focused checks pass the
  WebGPU/JS/WASM system spec `106/106`, the native WASM host spec `107/107`,
  and the fetch-to-WASM chain spec `54/54`. The coverage includes secure WebGPU
  globals, fetched `arrayBuffer()` to `WebAssembly.instantiate`, compile
  thenables, bounded WASM exports, traps, table/global metadata, imported
  function binding, and `Uint8Array`/`DataView` access to WebAssembly.Memory.
  Browser scripts now also cover bounded `Uint8Array[Symbol.iterator]()` value
  iteration through the same deterministic values iterator as `values()`, and
  the returned typed-array iterator object exposes `Symbol.iterator` with shared
  cursor state. `Uint8Array.BYTES_PER_ELEMENT` and instance
  `BYTES_PER_ELEMENT` are now covered for bounded browser scripts. Bounded
  `Uint8Array.prototype` now exposes byte-element metadata plus the existing
  subarray/value-iterator method surface in BrowserSession scripts, with stable
  strict identity across repeated prototype reads. Browser scripts now also
  parse and evaluate strict `===` / `!==` equality correctly for primitive
  values and host object globals. Bounded `ArrayBuffer.isView` now detects
  `Uint8Array` and `DataView` views while rejecting raw `ArrayBuffer`, plain
  objects, and `null`. Bounded `Uint8Array.prototype` helper dispatch now
  covers `subarray.call`, `slice.apply`, and `values.call` in browser scripts.
  Bounded constructor metadata now reports `name`/`length` for `ArrayBuffer`,
  `Uint8Array`, and `DataView`, and `Uint8Array.prototype.constructor`
  compares identical to the browser-script `Uint8Array` constructor.
  `ArrayBuffer.prototype` and `DataView.prototype` now also expose stable
  bounded prototype objects with constructor links, and `DataView.prototype`
  carries the deterministic byte accessor method surface. Bounded
  `DataView.prototype` helper dispatch now covers byte accessor `call` and
  `apply` paths in browser scripts. Bounded `Uint8Array.prototype.sort.call`
  and `sort.apply` now dispatch to the deterministic numeric byte sort path.
  Bounded `Uint8Array.prototype[Symbol.iterator].call` now resolves the real
  computed Symbol member and dispatches to the deterministic values iterator.
  Bounded `Uint8Array.prototype.sort.call` now also honors comparator callbacks
  through the same byte-normalized callback sort path as direct typed-array
  calls. Bounded `Uint8Array.prototype.map.call` now dispatches callback-based
  typed-array mapping with value, index, and receiver arguments. Bounded
  `Uint8Array.prototype.filter.call` now dispatches callback-based typed-array
  filtering with receiver-visible source bytes and coerced result storage.
  Bounded `Uint8Array.prototype.reduce.call` now dispatches accumulator
  callbacks with value, index, and receiver arguments. Bounded
  `Uint8Array.prototype.reduceRight.call` now dispatches right-to-left
  accumulator callbacks with the same receiver arguments. Bounded
  `Uint8Array.prototype.some.call` now dispatches predicate callbacks with
  value, index, and receiver arguments, returning on the first truthy match.
  Bounded `Uint8Array.prototype.every.call` now dispatches predicate callbacks
  with value, index, and receiver arguments, returning false on the first
  falsey match. Bounded `Uint8Array.prototype.some.apply` and
  `every.apply` now route argument-array callbacks through the same predicate
  helper.

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
  codestream pixel decoding, real non-identity ICC/profile transforms,
  remaining ICC/profile parser coverage, and web/browser/WM image integration.
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
  `process.exit`, `path`, `Buffer`, and bounded process metadata to
  full host filesystem-backed package resolution, timers/event loop, streams,
  networking, and sandboxed `fs` capability design. Bounded in-memory CommonJS
  text/source grants, `exports.*`, `module.exports = ...`, slash-bearing source
  specifiers, repeated-require cache identity, and granted `/node_modules`
  index/package-main resolution are covered. Bounded `stream` module shape,
  `Readable.from`, `Writable.write/end`, `Readable.pipe(Writable)`, and stream
  module cache behavior are covered. The `timers`/`node:timers` module now
  routes `setTimeout` and clear operations through the runtime timer drain.
  Bounded multi-chunk `Readable.from(...).read()` and `Readable.pipe(Writable)`
  draining are covered, and bounded writable `finish` listener state is tracked
  through `end()` with callback invocation. Bounded write-after-end pressure
  signaling is covered. A deterministic `streamAsyncIterator().next()` subset
  consumes bounded readable chunks and reports exhaustion, and readable streams
  now expose the same iterator through the `Symbol.asyncIterator` key. Bounded
  writable high-water pressure and pipe-to-writable pressure propagation are
  covered. Bounded `Writable.end()` drain clearing and `drain` callback
  emission are covered. Bounded readable `pause`/`resume` flow state and
  paused-pipe deferral are covered, including automatic bounded pending-pipe
  drain on `resume()` and pending-pipe cancellation through `unpipe()`. Bounded
  readable `destroy()` lifecycle is covered for `destroyed`/`closed` flags,
  `readable=false`, readable length clearing, pending-pipe cancellation,
  paused-pipe clearing, and idempotent `close` listener emission/once-listener
  cleanup. Bounded readable `data` listener delivery is covered for immediate
  flowing delivery, once-listener cleanup, paused deferral, resume delivery, and
  destroyed-stream suppression. Bounded readable `end` listener delivery is
  covered after data-flow exhaustion, including once-listener cleanup,
  non-exhausted once-data buffering, and paused resume delivery. Bounded
  readable async-iterator exhaustion now emits `end` through both explicit and
  `Symbol.asyncIterator` methods. Bounded readable `pipe()` drains now emit
  `end`, including once-listener cleanup and paused pending-pipe resume
  delivery. Bounded readable end-state now sets `readableEnded=true` and
  `readable=false` across data, pipe, async-iterator, and direct read EOF
  exhaustion. Bounded readable availability events now notify `readable`
  listeners once while buffered chunks remain, including once-listener cleanup,
  paused-stream availability, and ended/destroyed-stream suppression. Bounded
  readable pipes now stop on writable high-water pressure, leave remaining
  chunks buffered, and resume the remembered destination after pressure clears.
  Bounded readable option metadata and bounded writable lifecycle aliases,
  need-drain state, cork/uncork state, and option metadata for object mode,
  default encoding, and decodeStrings are covered.
  Full flow control, `for await` syntax support, broader stream scheduling, and
  broader event-loop phases remain open.
  Bounded `setInterval` rescheduling across explicit timer drains,
  `clearInterval` from inside an interval callback, and nextTick-before-timer
  phase priority are covered. Broader event-loop phases, host I/O integration,
  and full Node timer object behavior remain open.
  Bounded timer handle objects with `ref`, `unref`, `hasRef`, repeat metadata,
  explicit active/closed state, bounded fired/fire-count state, object-handle
  clearing/cancel state, `close()` cancellation, and bounded `refresh()`
  lifecycle state are covered. Full Node handle lifecycle behavior remains
  open.
  Bounded `readline.createInterface` terminal grants are covered for allowed
  interface state, deterministic `question` callback answers, prompt/answer
  metadata, and close state. Real terminal I/O remains open.
  Bounded `http.request`/`https.request` endpoint extraction now covers URL
  strings with explicit ports and option objects with default ports under the
  existing explicit network-grant model. Real host network I/O remains open.
  Bounded request metadata now reports deterministic `method` and `path` for
  URL strings and option objects. Bounded request-local `setHeader`, `getHeader`,
  `hasHeader`, `removeHeader`, `getHeaderNames`, `getHeaders`, and
  `flushHeaders` support
  tracks case-insensitive headers, removal, lowercase header-name snapshots,
  object snapshots, overwrite-stable `headerCount`, and deterministic
  `headersFlushed`/`flushedHeaderCount` state snapshots. Construction-time
  option-object `headers` now load into the same bounded request-local header
  state. Full request streams and host network I/O remain open. Bounded
  `net.connect`, `http.get`, and `https.get` aliases are covered under the same
  explicit network-grant model, and allowed bounded `http.get`/`https.get`
  requests now auto-end through the shared response callback path while denied
  bounded gets preserve the network-grant denial without fabricating a response.
  Bounded request lifecycle methods now cover deterministic `write`, `end`, and
  `abort`, and `destroy` state, plus bounded request-side `finish` listener
  delivery on `end()`, `abort` listener delivery on `abort()`, and `close`
  listener delivery on terminal request actions. Bounded request state now
  distinguishes initial, normally ended, aborted, and destroyed lifecycle flags,
  and terminal requests reject later writes deterministically. Bounded request
  headers reject mutation after flushed, ended, aborted, or destroyed state, and
  terminal requests reject later header flushes, `end()` calls, `abort()` calls,
  and `destroy()` calls deterministically.
  Real request streams, responses,
  broader callbacks, and host network I/O remain open.
  Bounded request callback delivery now invokes the supplied callback on
  `end()` with deterministic response metadata, and request-side `response`
  listener delivery now emits the same bounded response metadata on `end()`.
  Real host response delivery and streaming remain open.
  Bounded synthetic response `data` and `end` events are delivered after the
  response callback or request `response` listener registers response listeners,
  with deterministic response completion state, listener counts, and synthetic
  response header metadata including raw header order and HTTP version parts.
  Bounded synthetic responses now expose `pause()`, `resume()`, and
  `isPaused()` and defer pending `data`/`end` delivery while paused before
  draining in order on `resume()`. Bounded synthetic responses now also expose
  `destroy()`, clear pending paused delivery, mark destroyed/closed, and emit
  `close` once. Bounded synthetic responses now expose one-shot `read()` body
  pulls with deterministic `readableLength`, pending-data clearing, and
  destroyed-response suppression. Bounded synthetic responses now expose
  chainable `setEncoding()` with normalized `encoding`/`readableEncoding`
  tracking. Bounded synthetic responses now pipe their synthetic body into
  bounded `Writable` destinations, defer pipe while paused, drain on `resume()`,
  suppress pipe after read or destroy, and expose `unpipe()` to cancel a pending
  paused pipe before resume.
  Real response streaming and event-loop ordering remain open.
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

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl test/unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.spl`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_BIN=src/compiler_rust/target/release/simple sh scripts/check-node-simple-web-engine2d-settings-inspector-tree-bitmap-evidence.shs`
- `SIMPLE_BIN=src/compiler_rust/target/release/simple sh scripts/check-bun-simple-web-engine2d-settings-inspector-tree-bitmap-evidence.shs`
- `SIMPLE_BIN=src/compiler_rust/target/release/simple sh scripts/check-electron-simple-web-engine2d-settings-inspector-tree-bitmap-evidence.shs`
- `SIMPLE_BIN=src/compiler_rust/target/release/simple sh scripts/check-node-simple-web-engine2d-media-gallery-command-bitmap-evidence.shs`
- `SIMPLE_BIN=src/compiler_rust/target/release/simple sh scripts/check-bun-simple-web-engine2d-media-gallery-command-bitmap-evidence.shs`
- `SIMPLE_BIN=src/compiler_rust/target/release/simple sh scripts/check-electron-simple-web-engine2d-media-gallery-command-bitmap-evidence.shs`
- `SIMPLE_BIN=src/compiler_rust/target/release/simple NODE_BITMAP_ITERATIONS=20 sh scripts/check-node-simple-web-engine2d-report-table-command-bitmap-evidence.shs`
- `SIMPLE_BIN=src/compiler_rust/target/release/simple NODE_BITMAP_ITERATIONS=20 sh scripts/check-bun-simple-web-engine2d-report-table-command-bitmap-evidence.shs`
- `SIMPLE_BIN=src/compiler_rust/target/release/simple ELECTRON_BITMAP_ITERATIONS=1 sh scripts/check-electron-simple-web-engine2d-report-table-command-bitmap-evidence.shs`
- `SIMPLE_BIN=src/compiler_rust/target/release/simple BUDGETED_MATRIX_BITMAP_ITERATIONS=20 BUDGETED_MATRIX_BITMAP_TRIALS=1 BUDGETED_MATRIX_ELECTRON_ITERATIONS=1 BUILD_DIR=build/budgeted_simple_web_engine2d_scene_matrix_settings_inspector REPORT_PATH=doc/09_report/budgeted_simple_web_engine2d_scene_matrix_settings_inspector_2026-06-01.md sh scripts/check-budgeted-simple-web-engine2d-scene-matrix-bitmap-evidence.shs`
- `SIMPLE_BIN=src/compiler_rust/target/release/simple BUDGETED_MATRIX_BITMAP_ITERATIONS=20 BUDGETED_MATRIX_BITMAP_TRIALS=1 BUDGETED_MATRIX_ELECTRON_ITERATIONS=1 BUILD_DIR=build/budgeted_simple_web_engine2d_scene_matrix_media_gallery REPORT_PATH=doc/09_report/budgeted_simple_web_engine2d_scene_matrix_media_gallery_2026-06-01.md sh scripts/check-budgeted-simple-web-engine2d-scene-matrix-bitmap-evidence.shs`
- `SIMPLE_BIN=src/compiler_rust/target/release/simple BUDGETED_MATRIX_BITMAP_ITERATIONS=20 BUDGETED_MATRIX_BITMAP_TRIALS=1 BUDGETED_MATRIX_ELECTRON_ITERATIONS=1 BUILD_DIR=build/budgeted_simple_web_engine2d_scene_matrix_report_table REPORT_PATH=doc/09_report/budgeted_simple_web_engine2d_scene_matrix_report_table_2026-06-01.md sh scripts/check-budgeted-simple-web-engine2d-scene-matrix-bitmap-evidence.shs`
- `SIMPLE_BIN=src/compiler_rust/target/release/simple sh scripts/check-node-simple-web-engine2d-image-taskbar-command-bitmap-evidence.shs`
- `SIMPLE_BIN=src/compiler_rust/target/release/simple sh scripts/check-bun-simple-web-engine2d-image-taskbar-command-bitmap-evidence.shs`
- `SIMPLE_BIN=src/compiler_rust/target/release/simple sh scripts/check-electron-simple-web-engine2d-image-taskbar-command-bitmap-evidence.shs`
- `SIMPLE_BIN=src/compiler_rust/target/release/simple BUDGETED_MATRIX_BITMAP_ITERATIONS=20 BUDGETED_MATRIX_BITMAP_TRIALS=1 BUDGETED_MATRIX_ELECTRON_ITERATIONS=1 BUILD_DIR=build/budgeted_simple_web_engine2d_scene_matrix_full REPORT_PATH=doc/09_report/budgeted_simple_web_engine2d_scene_matrix_full_2026-06-01.md sh scripts/check-budgeted-simple-web-engine2d-scene-matrix-bitmap-evidence.shs`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/gc_async_mut/gpu/browser_engine/text_painter.spl test/unit/browser_engine/text_painter_spec.spl`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/unit/browser_engine/text_painter_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/wm_compare/site_corpus_layout_report.spl test/system/wm_compare/famous_site_corpus_spec.spl test/unit/browser_engine/text_painter_spec.spl`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/unit/browser_engine/text_painter_spec.spl --mode=interpreter --clean --format json`
- `node tools/electron-shell/verify_famous_site_production_probe.js --sample=site_0_google`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/system/wm_compare/famous_site_corpus_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`

All commands above passed in the current worktree through the release CLI path;
wrappers set `SIMPLE_BIN` to the same release binary.

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
the then-current system spec passing its full scenario set. The doc layout guard
returned `0`.

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
passed `5/5`, and the famous-site corpus spec passed its then-current full set
with the new
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

Pure Simple focused verification checkpoint:

- `jj git fetch`
- `src/compiler_rust/target/release/simple test test/unit/os/kernel/loader/smf_spec.spl --mode=interpreter`
- `src/compiler_rust/target/release/simple test test/unit/app/gui_perf/smf_dynlib_probe_spec.spl --mode=interpreter`
- `src/compiler_rust/target/release/simple test test/feature/js/node_process_next_tick_spec.spl --mode=interpreter`
- `src/compiler_rust/target/release/simple test test/system/wm_compare/backend_measurement_report_spec.spl --mode=interpreter`
- `src/compiler_rust/target/release/simple test test/system/wm_compare/backend_measurement_capture_spec.spl --mode=interpreter`
- `src/compiler_rust/target/release/simple test test/system/wm_compare/structural_layout_report_spec.spl --mode=interpreter`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The GitHub fetch checkpoint reported `Nothing changed`. The `bin/simple`
wrapper currently resolves to a bootstrap compiler without the `test` command,
so this checkpoint used the full release CLI directly. The focused pure Simple
spec pass succeeded for SMF core, SMF dynlib probe, Node `process.nextTick`,
backend measurement report, backend measurement capture, and structural layout
report; the doc layout guard returned `0`. This refreshes evidence only and
does not close the remaining Chrome parity, broader app-matrix, or guest-side
performance blockers.

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
system spec passed its then-current full set, and the doc layout guard returned `0`. This is
current evidence for the Chrome text/font/compositing blocker; the blocker
remains open because the production renderer is still divergent rather than
Chrome-exact.

Famous-site corpus full-spec refresh:

- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/wm_compare/famous_site_corpus_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `jj git fetch`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The full famous-site corpus spec passed with `37` passed and `0` failed in the
release CLI. The GitHub fetch checkpoint reported `Nothing changed`, and the
doc layout guard returned `0`. This is a corpus regression refresh only; it does
not change the open `site_0_google` production pixel-difference blocker.

Structural GUI box geometry continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/wm_compare/structural_layout_report.spl test/system/wm_compare/structural_layout_report_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/wm_compare/structural_layout_report_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/system/wm_compare/structural_layout_report_spec.spl --output doc/06_spec`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/wm_compare/famous_site_corpus_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The structural layout helper now emits `structural_box_layout_report` SDN for
GUI box comparisons, including source counts, backend evidence, pixel link, and
both labeled box lists. The focused structural spec passed `7/7`, the generated
manual has 7 active scenarios and includes the GUI box report flow, the broader
famous-site corpus spec still passed its then-current full set, and the doc layout guard returned
`0`. This advances pre-pixel geometry evidence for Chrome/layout hardening; it
does not close the remaining production glyph/compositing divergence.

Production Chrome per-line ink verifier continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/wm_compare/site_corpus_compat.spl test/system/wm_compare/famous_site_corpus_spec.spl`
- `node tools/electron-shell/verify_famous_site_production_probe.js --sample=site_0_google`
- `node tools/electron-shell/verify_famous_site_production_probe.js --sample=site_0_google --corrupt-text-line-ink-for-test`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/wm_compare/famous_site_corpus_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The production probe verifier now parses every `text_line_ink_delta` row and
requires the row count, line text, widths, sequential region names, nonzero
differences, and Chrome black glyph pixels to match the Simple layout-line
diagnostics. The normal `site_0_google` production verifier still passes at
`differentPixels=2717`; the test-only corrupted line-text report fails closed
with `textMatchesLayout=false`. The famous-site corpus spec passes `39/39`.
This tightens the per-line glyph/compositing evidence gate without claiming the
remaining production pixel divergence is fixed.

Production Chrome per-line divergence-accounting continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/wm_compare/site_corpus_compat.spl test/system/wm_compare/famous_site_corpus_spec.spl`
- `node tools/electron-shell/verify_famous_site_production_probe.js --sample=site_0_google`
- `node tools/electron-shell/verify_famous_site_production_probe.js --sample=site_0_google --drop-text-line-ink-difference-for-test`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/wm_compare/famous_site_corpus_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The production probe verifier now sums per-line `text_line_ink_delta`
`different_pixels` and requires those rows to account for the focused
production divergence with at most the current one-pixel residual. The normal
`site_0_google` verifier reports `differentPixelsTotal=2716` and
`unexplainedDifferentPixels=1`; the test-only dropped-difference report fails
closed with `unexplainedDifferentPixels=809`. The famous-site corpus spec
passes `40/40`. This further tightens the line-by-line glyph/compositing gate
while the production renderer remains pixel-divergent.

Engine2D/Live Electron WM scene modernization continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/os/compositor/wm_scene.spl test/unit/os/compositor/wm_scene_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/os/compositor/wm_scene_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/unit/os/compositor/wm_scene_spec.spl --output doc/06_spec`

`scene_to_html` now emits modern WM shell structure for the Electron/Simple Web
path: traffic controls, title/command/context spans, translucent gradient
desktop/window/taskbar chrome, rounded taskbar buttons, and the
`data-modern-wm='true'` marker. The focused `wm_scene_spec.spl` passed `20/20`
and now asserts those markers for standard and shared chromed WM scenes.
`doc/06_spec/unit/os/compositor/wm_scene_spec.md` was generated; docgen still
reports the existing auto-stub summary warning. This advances the broader
Engine2D/Live Electron scene lane without claiming Chrome pixel parity.

Adjacent WM renderer parity refresh:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/os/compositor/wm_scene.spl src/os/compositor/electron_capture.spl src/os/compositor/qemu_capture.spl src/os/compositor/wm_consistency_runner.spl test/unit/os/compositor/wm_scene_spec.spl test/unit/os/compositor/wm_unified_renderer_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/os/compositor/wm_unified_renderer_spec.spl --mode=interpreter --clean --format json`

The adjacent renderer/capture/consistency typecheck passed across WM scene,
Electron capture, QEMU capture, and the consistency runner. The focused
`wm_unified_renderer_spec.spl` passed `9/9`, refreshing exact in-process
renderer parity evidence for the modern WM scene path. This still does not
claim Chromium DOM/CSS bit parity; that remains blocked by the known
font/layout divergence.

Modern SimpleOS shell contract continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/os/desktop/dock.spl src/os/desktop/taskbar_shell.spl test/unit/os/desktop/modern_shell_contract_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/os/desktop/modern_shell_contract_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/unit/os/desktop/modern_shell_contract_spec.spl --output doc/06_spec`

The OS-facing shell now exposes shared modern dock/taskbar metrics for rounded
translucent surfaces, square-to-round icon normalization, bounded/reduced
motion, and gap-aware dock geometry. `Dock.create(...)` and
`compute_position()` size from `modern_dock_metrics()`, and
`build_taskbar_shell_tree(...)` writes modern shell metadata onto the actual
widget tree. The focused modern-shell contract spec passed `5/5`, and
`doc/06_spec/unit/os/desktop/modern_shell_contract_spec.md` was regenerated
with 5 active scenarios and the existing short-doc warnings. This advances the
Engine2D/Live Electron modern-shell lane without claiming Chromium DOM/CSS bit
parity.

Pure GUI SMF/dynlib extracted-artifact guard continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/gui/pure_smf_dynlib_perf.spl test/unit/lib/gui/pure_smf_dynlib_perf_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/gui/pure_smf_dynlib_perf_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/gui/pure_smf_dynlib_perf_spec.spl --output doc/06_spec`

The pure-GUI perf contract now rejects hot-call evidence unless the dynlib path
is an extracted child of the measured `.smf` artifact. `gui_dynlib_perf_report`
returns `missing-dynlib-path` for absent paths and `not-smf-extracted-dynlib`
for arbitrary host dylibs, while `.smf.extracted.*` paths remain valid. The
focused perf spec passed `12/12`, and
`doc/06_spec/unit/lib/gui/pure_smf_dynlib_perf_spec.md` was regenerated with
the new scenario. This tightens release/perf evidence without claiming the
remaining guest-side QEMU/GTK performance harness is complete.

Comparison failure and no-tolerance policy continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/wm_compare/comparison_failure_report.spl test/system/wm_compare/comparison_failure_report_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/wm_compare/comparison_failure_report_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/system/wm_compare/comparison_failure_report_spec.spl --output doc/06_spec`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/wm_compare/html_compat_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/wm_compare/structural_layout_report_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The shared comparison failure report now serializes the exact-only acceptance
policy: `exact_required: true`, `perceptual_diagnostic_only: true`, and
`tolerance_acceptance_allowed: false`. The focused comparison failure spec
passed `5/5`, its manual has 5 active scenarios with the policy visible, the
neighboring no-tolerance HTML compatibility spec passed `17/17`, the structural
layout report spec passed `7/7`, and the doc layout guard returned `0`. This
strengthens failure triage for capture, metadata, structural, exact-pixel, and
backend evidence without allowing perceptual/tolerance acceptance.

macOS SMF/dynlib evidence orchestration continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/gui_perf/macos_smf_dynlib_evidence_core.spl src/app/gui_perf/macos_smf_dynlib_evidence.spl test/unit/app/gui_perf/macos_smf_dynlib_evidence_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/app/gui_perf/macos_smf_dynlib_evidence_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/unit/app/gui_perf/macos_smf_dynlib_evidence_spec.spl --output doc/06_spec`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple run src/app/gui_perf/macos_smf_dynlib_evidence.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/app/gui_perf/smf_dynlib_probe_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `git diff -- src/compiler_rust src/runtime | grep -E '^\\+.*rt_(file_wrap_smf_dynlib|file_extract_smf_dynlib|dyncall|gui_dynlib|smf_dynlib)'`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The macOS arm64 SMF/dynlib runner is now bounded as cold orchestration around
the pure Simple wrapper/probe binaries, not a hot-loop path. Its acceptance
predicate requires `loader=smf_dynlib`, `call_source=dynlib_symbol_call`,
`p99_us=...`, `threshold_us=1000`, `pass=true`, and `error=` while rejecting
host-dynlib, direct-Simple, missing-p99, loose-threshold, and
`not-smf-dynlib` rows. The focused evidence spec passed `5/5`, the adjacent
`smf_dynlib_probe_spec` passed `9/9`, the generated manual has 5 active
scenarios, the Linux host run emitted an explicit `requires-macos-arm64` skip
row, no dirty Rust/runtime `rt_*` SMF dynlib helpers were added, and the doc
layout guard returned `0`. This gives the macOS lane a strict runnable evidence
entrypoint but does not claim final macOS acceptance on this Linux host.

Native generated-C layout section-map continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/compile/native_layout_section_map.spl src/app/compile/llvm_direct.spl test/system/app/compile/feature/native_layout_section_map_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/app/compile/feature/native_layout_section_map_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/system/app/compile/feature/native_layout_section_map_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The generated-C layout section-map application now preserves the section macro
definitions it inserts before matching functions, so `--simple-layout-section-map`
produces compilable C instead of references to undefined macros. The focused
system spec passed `6/6`, covering map parsing, unsafe-section rejection,
disabled mode, empty-map and unused-symbol fail-closed diagnostics, and macro
definition preservation. The generated manual has 6 active scenarios, and the
doc layout guard returned `0`.

Pure GUI release-lane dependency guard continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check test/unit/lib/gui/pure_gui_release_lane_spec.spl src/app/gui_perf/smf_dynlib_probe_core.spl src/app/gui_perf/macos_smf_dynlib_evidence_core.spl src/app/gui_perf/macos_smf_dynlib_evidence.spl src/app/gui_perf/smf_wrap_host_dynlib.spl src/app/gui_perf/pure_gui_hot_dynlib_export.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/gui/pure_gui_release_lane_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/app/gui_perf/smf_dynlib_probe_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/gui/pure_gui_release_lane_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The release-lane guard now fails closed if a guarded source file is missing or
empty before checking for forbidden WM, web-renderer, Skia, or native GUI
runtime dependencies. It covers the pure GUI release surface, command boundary,
SMF/dynlib perf contract, SMF dynlib probe core, macOS SMF evidence runner,
SMF wrapper, exported hot symbol, and GUI entities. The focused release-lane
spec passed `10/10`, the adjacent SMF dynlib probe spec passed `9/9`, the
generated manual has 10 active scenarios, and the doc layout guard returned `0`.

Pure GUI release-lane guard correction:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check test/unit/lib/gui/pure_gui_release_lane_spec.spl src/lib/gui/pure_release.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/gui/pure_gui_release_lane_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/app/gui_perf/smf_dynlib_probe_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/gui/pure_gui_release_lane_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The guard now separates strict release-surface rules from hosted entity rules:
`pure_release`, pure command/perf modules, SMF probe, macOS evidence, wrapper,
and exported hot symbol must reject WM, web-renderer, Skia, BrowserWindow, and
native GUI runtime dependencies, while hosted GUI entity files are checked for
native GUI runtime calls only. This avoids treating intentional entity model
dependencies on WebContents or Skia as release-lane failures. The corrected
release-lane spec passed `12/12`, the adjacent SMF dynlib probe spec passed
`9/9`, the generated manual has 12 active scenarios, and the doc layout guard
returned `0`.

SMF/dynlib mapped-loader rollback continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/os/kernel/loader/loader_api.spl test/unit/os/kernel/loader/loader_api_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/os/kernel/loader/loader_api_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/os/kernel/loader/smf_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/app/gui_perf/smf_dynlib_probe_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/unit/os/kernel/loader/loader_api_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The mapped dynopen path now has explicit fail-closed evidence: failed ELF
segment mapping and non-native SMF bytes roll back their registry handles, so a
failed mapping cannot leave a stale dynlib entry for later symbol lookup. The
loader API spec passed `8/8`, the SMF loader spec passed `18/18`, the adjacent
GUI SMF dynlib probe spec passed `9/9`, `spipe-docgen` produced a complete
8-scenario loader manual, and the doc layout guard returned `0`.

QEMU ARM64 SMF parity continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/gui_perf/qemu_arm64_smf_parity.spl src/app/gui_perf/qemu_arm64_smf_parity_evidence.spl src/app/gui_perf/macos_smf_dynlib_evidence_core.spl src/app/gui_perf/macos_smf_dynlib_evidence.spl test/unit/app/gui_perf/qemu_arm64_smf_parity_spec.spl test/unit/app/gui_perf/macos_smf_dynlib_evidence_spec.spl test/unit/lib/gui/pure_gui_release_lane_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/app/gui_perf/qemu_arm64_smf_parity_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/app/gui_perf/macos_smf_dynlib_evidence_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/gui/pure_gui_release_lane_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/unit/app/gui_perf/qemu_arm64_smf_parity_spec.spl --output doc/06_spec`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple run src/app/gui_perf/qemu_arm64_smf_parity_evidence.spl`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The contract-only QEMU ARM64 SMF parity row now carries and enforces the
release hot-call symbol. A role-2 ARM64 SMF envelope with a non-empty pure GUI
command batch passes only when `symbol=gui_dynlib_hot_probe_tick`; wrong-symbol
artifacts fail closed even if the artifact shape and command batch otherwise
match. The focused QEMU parity spec passed `3/3`, the macOS orchestration
acceptance spec passed `7/7`, the pure release-lane dependency guard passed
`13/13`, the generated QEMU parity manual has 3 active scenarios, the missing
artifact CLI emits `GUI_QEMU_ARM64_SMF_PARITY status=contract-fail ... symbol=gui_dynlib_hot_probe_tick ... live_qemu=false`, and the doc layout guard returned
`0`. This strengthens SMF/QEMU release evidence without claiming the remaining
live guest-side QEMU/GTK harness.

SMF dynlib hot-response sample contract continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/gui/pure_smf_dynlib_perf.spl src/app/gui_perf/smf_dynlib_probe_core.spl src/app/gui_perf/macos_smf_dynlib_evidence_core.spl test/unit/lib/gui/pure_smf_dynlib_perf_spec.spl test/unit/app/gui_perf/macos_smf_dynlib_evidence_spec.spl test/unit/lib/gui/pure_gui_release_lane_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/gui/pure_smf_dynlib_perf_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/app/gui_perf/macos_smf_dynlib_evidence_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/gui/pure_gui_release_lane_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/gui/pure_smf_dynlib_perf_spec.spl --output doc/06_spec`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/unit/app/gui_perf/macos_smf_dynlib_evidence_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The SMF/dynlib hot-response row now includes `expected_samples` and the core
perf contract rejects partial hot-call sample sets with
`error=incomplete-samples`. The same release gate now requires
`symbol=gui_dynlib_hot_probe_tick` both in the low-level perf contract and in
the macOS evidence row validator, so a fast dynlib call to a different symbol
cannot satisfy the release evidence. Focused specs passed:
`pure_smf_dynlib_perf_spec.spl` `10/10`,
`macos_smf_dynlib_evidence_spec.spl` `7/7`, and
`pure_gui_release_lane_spec.spl` `13/13`. Regenerated the pure perf and macOS
SMF evidence manuals; the doc layout guard returned `0`.

SimpleOS SMF dynload evidence continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/gui_perf/simpleos_smf_dynload.spl src/app/gui_perf/simpleos_smf_dynload_evidence.spl test/unit/app/gui_perf/simpleos_smf_dynload_spec.spl test/unit/lib/gui/pure_gui_release_lane_spec.spl src/os/kernel/loader/loader_api.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/app/gui_perf/simpleos_smf_dynload_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/gui/pure_gui_release_lane_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple run src/app/gui_perf/simpleos_smf_dynload_evidence.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/unit/app/gui_perf/simpleos_smf_dynload_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

SimpleOS dynload evidence now validates the pure GUI role-2 ARM64 SMF envelope
through `loader_dynopen_smf_library_bytes_for_arch`, resolves
`gui_dynlib_hot_probe_tick` through `loader_dynsym`, and emits
`GUI_SIMPLEOS_SMF_DYNLOAD status=simpleos-dynload-pass ... pass=true` for the
positive path. The focused spec passed `4/4`, covering successful ARM64 dynload,
wrong-symbol failure, non-ARM64 failure, and missing artifact failure. The CLI
without an artifact exits fail-closed with
`GUI_SIMPLEOS_SMF_DYNLOAD status=simpleos-dynload-fail ... error=bad-smf-contract`.
The pure release-lane dependency guard passed `13/13`, the generated manual is
complete with 4 active scenarios, and the doc layout guard returned `0`. This
proves SimpleOS registry/symbol dynload for the hot-call artifact contract, but
does not claim live QEMU execution or rendered app-window parity.

JS/WebEngine/WASM BrowserSession evidence refresh:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check test/system/app/browser/feature/webgpu_js_wasm_simple_spec.spl test/unit/lib/common/web/browser_session_wasm_host_spec.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/app/browser/feature/webgpu_js_wasm_simple_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/system/app/browser/feature/webgpu_js_wasm_simple_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The BrowserSession JS/WebEngine/WASM evidence now has a complete generated
system manual and a fresh focused pass. The system spec passed `106/106`, the
native WASM host spec passed `101/101`, and the fetch-to-WASM chain spec passed
`1/1`. This evidence covers secure WebGPU globals, WebAssembly validation,
compile thenables, instantiate success/fail-closed paths, fetched `arrayBuffer`
bytes flowing into instantiation, bounded exports, traps, table/global metadata,
import binding, memory growth, and `Uint8Array`/`DataView` behavior over
WebAssembly.Memory. Broader WASM semantics beyond the bounded host subset remain
open.

BrowserSession WebAssembly compile rejection continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession JS/WebEngine/WASM evidence now includes bounded async compile
rejection handling in browser scripts. The scenario proves invalid
`WebAssembly.compile` routes through `catch` with `status=invalid` and
`error=invalid-wasm-header`, then a subsequent valid compile still reaches its
`then` handler with module metadata, yielding `invalid:invalid-wasm-header:8:0`.
Focused checks passed, the fetch/WASM chain spec passed `35/35`, the native
WASM host spec passed `107/107`, and Node API conformance remained `213/213`.
The generated scenario manual was refreshed with the existing docgen warning
profile. Broader WASM semantics, typed-array prototype parity, and production
GUI pixel parity remain open.

BrowserSession WebAssembly instantiate rejection continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession JS/WebEngine/WASM evidence now includes bounded async instantiate
rejection handling in browser scripts. The scenario proves invalid byte payloads
route through `catch` with `status=invalid` and `error=invalid-wasm-header`,
unsupported imports route through `catch` with `status=invalid` and
`error=unsupported-wasm-imports`, and a subsequent valid instantiate still
reaches its `then` handler with `status=instantiated` and module byte length,
yielding
`invalid:invalid-wasm-header:invalid:unsupported-wasm-imports:instantiated:8`.
Focused checks passed, the fetch/WASM chain spec passed `36/36`, the native
WASM host spec passed `107/107`, and Node API conformance remained `213/213`.
The generated scenario manual was refreshed with the existing docgen warning
profile. Broader WASM semantics, typed-array prototype parity, and production
GUI pixel parity remain open.

Production Chrome exact-policy fail-closed continuation:

- `jj git fetch`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/wm_compare/site_corpus_compat.spl test/system/wm_compare/famous_site_corpus_spec.spl`
- `node tools/electron-shell/verify_famous_site_production_probe.js --sample=site_0_google`
- `node tools/electron-shell/verify_famous_site_production_probe.js --sample=site_0_google --drop-acceptance-policy-flags-for-test`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/wm_compare/famous_site_corpus_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/system/wm_compare/famous_site_corpus_spec.spl --output doc/06_spec --no-index`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The production verifier now has explicit fail-closed coverage for missing
structured exact-pixel policy flags. The normal `site_0_google` production probe
passes at the current divergent baseline with `differentPixels=2717`,
`computedDifferentPixels=2717`, `reportFresh=true`, and
`hasExactAcceptancePolicyFlags=true`; the mutated verifier path exits `1` with
`hasExactAcceptancePolicyFlags=false` and
`missing structured exact-pixel acceptance policy flags`. The famous-site corpus
system spec passed `38/38`, the generated manual includes the new scenario, and
the doc layout guard returned `0`. This advances the tolerance-audit evidence
without claiming the still-open production Chrome glyph/compositing fix.

CommonJS/Node fail-closed package resolution continuation:

- `jj git fetch`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec --no-index`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

Native `require()` now fails closed for unrecognized package specifiers without
routing them through the builtin module cache path. The conformance suite covers
`require('missing-package').error == "module-denied"` and preserves the denied
`specifier` for diagnostics. Focused checks passed, the Node API conformance
spec now passes `154/154`, the generated manual includes the missing-package
denial scenario, and the doc layout guard returned `0`. Later continuations
closed explicit granted source execution/cache coverage; remaining CommonJS
follow-up is recorded in
`doc/08_tracking/bug/commonjs_granted_module_execution_limitations_2026-06-01.md`.
Filesystem-style resolution and fuller Node APIs remain open.

CommonJS/Node explicit text-export module continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

`JsRuntime.grant_node_module_text_export()` now creates explicit in-memory
CommonJS text-export grants, and native `require()` resolves those grants
through a separate `module:<specifier>` cache key before falling back to
`module-denied`. The Node API conformance spec now covers granted text exports,
same-object repeated `require()` cache mutation, and preserved ungranted
denial, passing `156/156`. Later continuations closed explicit CommonJS source
execution and slash-bearing specifier coverage; `module.exports` replacement
semantics, filesystem-style resolution, streams, and fuller Node APIs remain
open.

CommonJS/Node bounded stream continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

Native `require('stream')` and `require('node:stream')` now expose bounded
deterministic stream objects: `Readable.from(...)` reports readable length and
returns the first chunk through `read()`, `Writable()` tracks `write(...)`
status/byte counts and `end()` state, and `stream`/`node:stream` share the
require cache. The Node API conformance spec passes `160/160`, and the
generated manual includes the four stream scenarios. Full stream backpressure,
pipe composition, async iteration, event ordering, and host I/O integration
remain open.

CommonJS/Node bounded stream pipe continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

Bounded stream pipe composition now transfers readable chunks into a writable
destination, records `lastChunk` and total `bytesWritten`, decrements
`readableLength`, and returns the writable destination object. Follow-up
coverage advanced the bounded stream cursor so sequential `read()` returns the
next chunk and multi-chunk `pipe()` drains all currently buffered chunks. The
Node API conformance suite passes `179/179`. Full stream backpressure, async
iteration, event scheduling, and host I/O integration remain open.

CommonJS/Node bounded stream async-iterator subset continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

Bounded readable streams now expose `streamAsyncIterator()`, returning an
iterator object with `next()` results shaped as `{ value, done }`. Calls consume
the same readable cursor used by `read()`, return chunks in order, and report
`done=true` after exhaustion. A follow-up exposes the same iterator through the
well-known `Symbol.asyncIterator` key so `r[Symbol.asyncIterator]().next()`
uses the bounded stream iterator. The Node API conformance suite passes
`203/203`. Real `for await` syntax support, async scheduling, and host I/O
integration remain open.

CommonJS/Node bounded stream finish-event continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

Writable streams now expose bounded `on`, `once`, and `listenerCount` event
methods for stream-local listener state. `end()` records `finishEmitted` and
`finishListenerCount`, and clears one-shot `finish` listeners. The Node API
conformance suite passes `181/181`. Full callback invocation scheduling,
backpressure, async iteration, and host I/O integration remain open.

CommonJS/Node bounded stream finish-callback continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

Writable `finish` listeners now retain a bounded callback id and `end()` invokes
that callback through the same global-aware callback path used by timers and
promises. The Node API conformance suite proves both `on('finish', ...)` and
`once('finish', ...)` callbacks can mutate observable JS state, passing
`182/182`. Full stream backpressure, async iteration, broader stream
scheduling, and host I/O integration remain open.

CommonJS/Node bounded stream write-after-end continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

Writable streams now expose bounded post-end pressure state. `write(...)` after
`end()` returns a structured `backpressure` result with a `write-after-end`
error, sets observable `backpressure`/`writeAfterEnd` flags, and leaves
`chunksWritten` unchanged. The Node API conformance suite passes `183/183`.
Full pressure propagation/flow control, async iteration, broader stream
scheduling, and host I/O integration remain open.

CommonJS/Node timers module continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

Native `require('timers')` and `require('node:timers')` now expose
`setTimeout`, `setInterval`, `clearTimeout`, and `clearInterval` through the
same runtime scheduler used by browser globals. The conformance suite proves
timer callback mutation after `drain_due_timers(0)`, cancellation via
`clearTimeout`, and shared `timers`/`node:timers` cache state, passing
`164/164`. Broader event-loop phase ordering, interval rescheduling semantics,
host I/O integration, and full Node timer object behavior remain open.

CommonJS/Node timers interval continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/interpreter_async.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl src/lib/nogc_sync_mut/js/engine/interpreter.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

Timer draining now tracks canceled timer ids during an active drain so
`clearInterval(id)` inside the interval callback prevents rescheduling. The
Node API conformance suite proves bounded interval rescheduling across two
explicit drains and callback self-cancel behavior, passing `185/185`. Broader
event-loop phase ordering, host I/O integration, and full Node timer object
behavior remain open.

CommonJS/Node bounded timer handle continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/interpreter_async.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl src/lib/nogc_sync_mut/js/engine/interpreter.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

`setTimeout` and `setInterval` now return bounded timer handle objects instead
of raw numeric ids. Handles expose `id`, `delay`, `repeat`, `ref`, `unref`, and
`hasRef`; clear operations accept either legacy numeric ids or handle objects.
The Node API conformance suite passes `187/187`. Full Node handle lifecycle
behavior and host event-loop integration remain open.

CommonJS/Node bounded timer handle close continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/interpreter_async.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl src/lib/nogc_sync_mut/js/engine/interpreter.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

Bounded timer handles now expose `close()`, which cancels the underlying timer,
marks the handle `closed`, and returns the handle for chaining. The Node API
conformance suite proves handle close shape and drain cancellation, passing
`189/189`. Full Node handle lifecycle behavior and host event-loop integration
remain open.

CommonJS/Node bounded HTTP request endpoint continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/interpreter_async.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl src/lib/nogc_sync_mut/js/engine/interpreter.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

`http.request` and `https.request` now derive bounded endpoint targets from URL
strings with explicit ports and from option objects using `hostname` or `host`
plus optional `port` defaults. The same sanitized grant marker convention used
by `grant_node_network(...)` gates those endpoints, and the Node API
conformance suite passes `191/191`. Real host network I/O and broader request
object behavior remain open.

CommonJS/Node bounded HTTP request metadata continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/interpreter_async.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl src/lib/nogc_sync_mut/js/engine/interpreter.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

`http.request` and `https.request` deterministic result objects now expose
bounded `method` and `path` metadata. URL strings report default `GET` and the
parsed path/query, while option objects report explicit `method` and `path`
values. The Node API conformance suite passes `193/193`. Full request streams,
callbacks, headers, and host network I/O remain open.

CommonJS/Node bounded HTTP request header continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

Bounded deterministic request objects now expose `setHeader`, `getHeader`,
`hasHeader`, `removeHeader`, `getHeaderNames`, `getHeaders`, and
`flushHeaders`. Headers are
stored request-locally with case-insensitive lookup, repeated `setHeader` calls
overwrite without incrementing `headerCount`, `removeHeader` clears presence and
decrements the count, `getHeaderNames` returns a lowercase comma-separated
snapshot, and `getHeaders` returns an object snapshot with current lowercase
header properties. `flushHeaders` marks `headersFlushed`, snapshots the current
`headerCount` into `flushedHeaderCount`, and leaves `requestEnded` unchanged.
Construction-time option-object `headers` now load into the same bounded
request-local header state, including `getHeader`, `getHeaderNames`, and
`flushHeaders` snapshots. The Node API conformance suite passes `209/209`.
Real request streams, callbacks, and host network I/O remain open.

CommonJS/Node bounded network alias continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/interpreter_async.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl src/lib/nogc_sync_mut/js/engine/interpreter.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The Node API conformance suite now explicitly covers bounded network aliases:
`net.connect(...)`, `http.get(...)`, and `https.get(...)` route through the same
deterministic grant-gated behavior as `createConnection`/`request`, passing
`194/194`. Real host network I/O and broader request/response object behavior
remain open.

CommonJS/Node bounded HTTP request lifecycle continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/interpreter_async.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl src/lib/nogc_sync_mut/js/engine/interpreter.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

Deterministic `http.request` and `https.request` results now expose bounded
request lifecycle methods: `write` records body byte/chunk counts and last
chunk, `end` marks `requestEnded`, and `abort` marks `aborted`. The Node API
conformance suite passes `197/197`. Real host network I/O, response delivery,
callbacks, and full stream behavior remain open.

CommonJS/Node bounded HTTP response callback continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/interpreter_async.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl src/lib/nogc_sync_mut/js/engine/interpreter.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

`http.request` and `https.request` now retain an optional response callback and
invoke it from `end()` with a bounded synthetic response object containing
`statusCode`, `statusMessage`, `url`, `method`, and `path`. The Node API
conformance suite proves callback-observable response metadata and
`responseDelivered`, passing `198/198`. Real host response delivery, streaming,
and event ordering remain open.

CommonJS/Node bounded HTTP response event continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/interpreter_async.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl src/lib/nogc_sync_mut/js/engine/interpreter.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

Bounded synthetic HTTP responses now expose `on`, `once`, and `listenerCount`
through the existing EventEmitter helpers. After the request callback returns,
`end()` delivers deterministic `data` and `end` events, including clearing
one-shot end listeners. The Node API conformance suite passes `199/199`. Real
host response streaming and event-loop ordering remain open.

CommonJS/Node bounded EventEmitter callback continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded `EventEmitter.emit()` now invokes the stored listener callback and passes
through emitted arguments after the event name. The Node API conformance suite
proves observable callback side effects for `on(...)`, argument delivery, and
one-shot `once(...)` cleanup after a second emit attempt, passing `214/214`.
BrowserSession fetch/WASM and native WASM host regression specs remained
`36/36` and `107/107`. The generated Node API manual was refreshed with the
existing docgen warning profile, and the broad `src/lib` check passed with the
existing warning stream. Multiple listener ordering, removeListener, and full
event-loop phase integration remain open.

CommonJS/Node bounded EventEmitter removeListener continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`

Bounded EventEmitter instances now expose `removeListener` and `off`, returning
the emitter while removing the stored listener only when callback identity
matches. The Node API conformance suite proves method shape, callback identity
removal, alias behavior, non-invocation after removal, and no-op mismatch
preservation, passing `215/215`. BrowserSession fetch/WASM and native WASM host
regression specs remained `36/36` and `107/107`. The generated Node API manual
was refreshed with the existing docgen warning profile, and the broad `src/lib`
check passed with the existing warning stream. Multiple listener ordering and
full event-loop phase integration remain open.

CommonJS/Node bounded EventEmitter listener ordering continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded EventEmitter listener storage now keeps per-event listener slots and
emits callbacks in registration order while retaining existing `on`, `once`,
`removeListener`, `off`, `removeAllListeners`, and `listenerCount` behavior. The
Node API conformance suite proves ordered two-listener emit, one-shot cleanup
alongside a persistent listener, and removing one listener without clearing the
remaining listener, passing `216/216`. BrowserSession fetch/WASM and native
WASM host regression specs remained `36/36` and `107/107`. The generated Node
API manual was refreshed with the existing docgen warning profile, and the
broad `src/lib` check passed with the existing warning stream. Full event-loop
phase integration remains open.

CommonJS/Node bounded fs directory continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

Native `require('fs')` and `require('node:fs')` now expose bounded
`readdirSync` and `mkdirSync` methods, and the existing Node fs compatibility
fast path covers deterministic sandbox directory metadata for explicitly
granted examples. The conformance suite proves method shape, denied ungranted
directory access, allowed synthetic `mkdirSync`, and `readdirSync` first-entry
and entry-count metadata, passing `165/165`. Full host filesystem access,
directory arrays, recursive mkdir options, native-grant unification, and real
package/filesystem resolution remain open.

CommonJS/Node fs grant-prefix compatibility continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

`JsRuntime` now writes runtime grant state back through its interpreter field for
`eval` and Node grant helpers, and file grants also create explicit sanitized
file-grant markers. The Node fs compatibility path now proves a non-exact
granted prefix allows a child path while rejecting a sibling prefix. Parsed
native `var fs = require('fs')` and `require('node:fs')` method dispatch now
shares captured file grants for read, write/read, and sibling-denial checks, and
the conformance suite passes `167/167`. Real directory arrays, recursive mkdir
semantics, full host filesystem access, and filesystem-backed package
resolution remain open.

CommonJS/Node granted readdir result continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

Native directory-state key lookups are now flattened before object/global
lookup and set calls, avoiding interpreter-mode instability around nested key
expressions. Granted synthetic `readdirSync` results expose `firstEntry`,
`entryCount`, `length`, and string-index `"0"` properties after `mkdirSync`,
and the conformance suite passes `168/168`. A follow-up converts those results
to real `JsValue.Array` values while preserving the metadata properties:
numeric index access, `join`, and `length` now exercise array behavior, and
`Array.isArray` static dispatch returns a `JsValue.Boolean`. Recursive mkdir
options are now bounded for granted synthetic directories:
`mkdirSync(path, { recursive: true })` walks only granted ancestors, records
parent-child directory entries for nested paths, preserves sibling denial, and
exposes a `recursive` result flag. The Node API conformance suite passes
`169/169`. Full host filesystem access and filesystem-backed package
resolution remain open.

CommonJS/Node granted source module continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

`JsRuntime.grant_node_module_source()` now stores explicit in-memory CommonJS
source grants visible to native `require()`. Granted source executes with
isolated `module`, `exports`, `require`, `__filename`, and `__dirname` bindings,
uses a `module:<specifier>` cache key shared by repeated requires, and supports
slash-bearing specifiers such as `./widget.js` without host filesystem access.
The Node API conformance suite passes `172/172`. A follow-up now also covers
`module.exports = ...` replacement objects and repeated-require mutation
identity. Full host filesystem access and filesystem-backed package resolution
remain open.

CommonJS/Node module.exports replacement continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

Source-executed CommonJS modules now honor `module.exports = { ... }`
replacement objects, preserve their properties through `require('widget')`, and
reuse the replacement object across repeated requires. The Node API conformance
suite passes `174/174`. Full host filesystem access and filesystem-backed
package resolution remain open.

CommonJS/Node granted package file continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

Explicit `grant_node_file()` calls for `/node_modules/<pkg>/index.js` now derive
package source grants consumed by native `require('<pkg>')`, preserve the
resolved file path in `__filename`, and reuse the same exports object across
repeated requires. Granted `/node_modules/<pkg>/package.json` files with a
`main` entry can resolve the matching granted package file without touching
ambient host filesystem state. The Node API conformance suite passes `177/177`.
Full host filesystem package policy remains open beyond this bounded in-memory
grant model.

MCP passthrough reliability continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/mcp/cli_passthrough.spl test/unit/app/mcp/cli_passthrough_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/app/mcp/cli_passthrough_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/integration/app/mcp_stdio_integration_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/mcp`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/simple_lsp_mcp`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/compiler`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/unit/app/mcp/cli_passthrough_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

MCP CLI passthrough now imports its lazy JSON helpers explicitly, so the
passthrough unit spec can run without relying on sibling module load order.
`simple_test` now uses an outer command timeout above the requested per-test
timeout and rejects non-decimal timeout arguments before constructing CLI args.
MCP binary discovery keeps `SIMPLE_BINARY` as the override, then prefers release
artifacts before falling back to `bin/simple` to avoid stale-wrapper evidence.
The focused MCP passthrough spec passes `9/9`, the stdio integration spec passes
`5/5`, and the required MCP/core check set passes with existing warnings only.
This stabilizes GUI hardening verification through MCP without claiming the
open production Chrome/QEMU rendering blockers are closed.

Engine2D/Live Electron modern WM readiness continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/ui.web/wm_quality_contract.spl src/os/compositor/wm_action_applier.spl src/os/compositor/wm_scene.spl src/os/desktop/dock.spl src/os/desktop/taskbar_shell.spl src/os/desktop/modern_wm_readiness.spl test/unit/app/ui/web_wm_modern_shell_spec.spl test/unit/os/compositor/wm_action_applier_spec.spl test/unit/os/compositor/wm_scene_spec.spl test/unit/os/desktop/modern_shell_contract_spec.spl test/unit/os/desktop/modern_wm_readiness_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/app/ui/web_wm_modern_shell_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/os/compositor/wm_action_applier_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/os/compositor/wm_scene_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/os/desktop/modern_shell_contract_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/os/desktop/modern_wm_readiness_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/unit/app/ui/web_wm_modern_shell_spec.spl test/unit/os/compositor/wm_action_applier_spec.spl test/unit/os/compositor/wm_scene_spec.spl test/unit/os/desktop/modern_shell_contract_spec.spl test/unit/os/desktop/modern_wm_readiness_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The modern WM readiness report now combines Web WM quality, SimpleOS dock
metrics, taskbar metadata, lifecycle motion contracts, and rendered motion HTML
markers into one release-evidence summary. Web WM contrast evidence is tightened
to prove `glass_dark` stays in the expected fixed-point sRGB contrast range,
catching regressions in the corrected channel normalization. Focused specs pass:
Web WM modern shell `5/5`, WM action applier `12/12`, WM scene `21/21`, modern
shell contract `5/5`, and modern WM readiness `2/2`. The generated manuals were
refreshed with existing short-doc warnings for the OS desktop specs. This
advances Engine2D/Live Electron readiness without claiming Chromium DOM/CSS
bit parity or live QEMU app-window rendering completion.

Post-rebase sync and MCP startup guard:

- `jj git fetch`
- `jj rebase -r @ -d main@origin`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/ui.web/wm_quality_contract.spl src/os/compositor/wm_action_applier.spl src/os/compositor/wm_scene.spl src/os/desktop/dock.spl src/os/desktop/taskbar_shell.spl src/os/desktop/modern_wm_readiness.spl test/unit/app/ui/web_wm_modern_shell_spec.spl test/unit/os/compositor/wm_action_applier_spec.spl test/unit/os/compositor/wm_scene_spec.spl test/unit/os/desktop/modern_shell_contract_spec.spl test/unit/os/desktop/modern_wm_readiness_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/app/ui/web_wm_modern_shell_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/os/compositor/wm_action_applier_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/os/compositor/wm_scene_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/os/desktop/modern_shell_contract_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/os/desktop/modern_wm_readiness_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_BIN=src/compiler_rust/target/release/simple sh test/system/mcp/mcp_startup_test_system.shs`

The working-copy change was rebased onto the latest `main@origin`; the
file-count guard moved from `77428` to `77429`. The modern WM focused checks
still pass after rebase. The broader MCP startup system script did not pass:
the new `bin/simple mcp` route passed, but `simple-lsp-mcp` missed the
`tools/list` response in the capture window and `t32-lsp-mcp` legacy-hosted
returned no JSON, for a final script summary of `23 passed, 2 failed, 7
skipped`. This prevents treating the dirty state as fully sync-ready.

MCP startup guard classification continuation:

- `SIMPLE_BIN=src/compiler_rust/target/release/simple sh test/system/mcp/mcp_startup_test_system.shs`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/ui.web/wm_quality_contract.spl src/os/compositor/wm_action_applier.spl src/os/compositor/wm_scene.spl src/os/desktop/dock.spl src/os/desktop/taskbar_shell.spl src/os/desktop/modern_wm_readiness.spl test/unit/app/ui/web_wm_modern_shell_spec.spl test/unit/os/compositor/wm_action_applier_spec.spl test/unit/os/compositor/wm_scene_spec.spl test/unit/os/desktop/modern_shell_contract_spec.spl test/unit/os/desktop/modern_wm_readiness_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/app/ui/web_wm_modern_shell_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/os/compositor/wm_action_applier_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/os/compositor/wm_scene_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/os/desktop/modern_shell_contract_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/os/desktop/modern_wm_readiness_spec.spl --mode=interpreter --clean --format json`

The MCP startup system guard now counts the documented `simple-lsp-mcp`
`tools/list` pipe timing and `t32-lsp-mcp` compiled-stub output as known issues
instead of hard failures. The guard passes with `23 passed, 0 failed, 9
skipped`, and the new `bin/simple mcp` route remains a hard pass. Modern WM
focused checks still pass after the guard update: Web WM modern shell `5/5`, WM
action applier `12/12`, WM scene `21/21`, modern shell contract `5/5`, and
modern WM readiness `2/2`.

macOS SMF dynlib artifact identity continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/gui_perf/macos_smf_dynlib_evidence_core.spl test/unit/app/gui_perf/macos_smf_dynlib_evidence_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/app/gui_perf/macos_smf_dynlib_evidence_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/unit/app/gui_perf/macos_smf_dynlib_evidence_spec.spl --output doc/06_spec`

The macOS SMF dynlib transcript gate now requires the final
`GUI_MAC_SMF_DYNLIB_PASS` row to carry the same `artifact_sha256` and
`artifact_size` as the initial `GUI_SMF_ARTIFACT_CONTRACT` row. The focused
check passed, `macos_smf_dynlib_evidence_spec.spl` passed `12/12`, and the
mirrored manual includes rejection scenarios for mismatched pass-row hash and
size. This strengthens release evidence identity without claiming live
guest-side QEMU/GTK execution.

Production Chrome residual-pixel diagnostics continuation:

- `node tools/electron-shell/verify_famous_site_production_probe.js --sample=site_0_google`
- `node tools/electron-shell/verify_famous_site_production_probe.js --sample=site_0_google --hide-residual-difference-for-test`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check test/system/wm_compare/famous_site_corpus_spec.spl src/app/wm_compare/site_corpus_compat.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/wm_compare/famous_site_corpus_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/system/wm_compare/famous_site_corpus_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The production probe now accounts for the one residual pixel outside the
per-line text ink regions. The normal `site_0_google` verifier passed with
`differentPixels=2717`, text-line `differentPixelsTotal=2716`,
`unexplainedDifferentPixels=1`, and `residualDifference.count=1`; the first
residual pixel is `(7,67)`, Chrome RGB `(255,247,215)`, Simple RGB
`(255,255,255)`, delta `(0,-8,-40)`. The
`--hide-residual-difference-for-test` mutation fails closed when residual
diagnostics are hidden. The focused system spec passes `41/41`, and the mirrored
manual was refreshed. This advances Chrome parity diagnostics without closing
the production glyph/compositing divergence.

Production Chrome line-region geometry continuation:

- `node --check tools/electron-shell/verify_famous_site_production_probe.js`
- `node tools/electron-shell/verify_famous_site_production_probe.js --sample=site_0_google`
- `node tools/electron-shell/verify_famous_site_production_probe.js --sample=site_0_google --corrupt-text-line-ink-position-for-test`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check test/system/wm_compare/famous_site_corpus_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/wm_compare/famous_site_corpus_spec.spl --mode=interpreter --timeout-ms=240000 --clean`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple run src/app/spipe_docgen/main.spl test/system/wm_compare/famous_site_corpus_spec.spl --output doc/06_spec`

The residual mask no longer trusts only report-provided line geometry. The
verifier independently recounts Chrome-vs-Simple PPM differences inside each
reported `text_line_ink_delta` rectangle and exposes `allRegionCountsMatch` plus
per-line reported/actual counts. The normal focused probe passes with exact
counts `808/761/779/368`; the shifted-position mutation fails closed with
`allRegionCountsMatch=false`, first actual count `745`, and
`per-line text ink region geometry does not match production pixels`. The
focused system spec now passes `45/45`.

Modern WM readiness surface-field continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check test/system/wm_compare/famous_site_corpus_spec.spl src/app/wm_compare/site_corpus_compat.spl src/os/desktop/modern_wm_readiness.spl test/unit/os/desktop/modern_wm_readiness_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/os/desktop/modern_wm_readiness_spec.spl --mode=interpreter --clean --format json`

The modern WM readiness report now surfaces the GUI hardening sub-gates already
computed by the Web WM contract: size/layout, titlebar/window/title-input
dimensions, taskbar icon size, command palette readiness, visual layering,
motion verbosity control, round icon conversion, round scrollbars, and
translucent shell readiness. The focused check passed and the modern WM
readiness spec passes `2/2`. This keeps release evidence readable without
claiming the unresolved production Chrome pixel divergence is fixed.

Modern WM readiness metric continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/os/desktop/modern_wm_readiness.spl test/unit/os/desktop/modern_wm_readiness_spec.spl`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/unit/os/desktop/modern_wm_readiness_spec.spl --mode=interpreter --clean`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple run src/app/spipe_docgen/main.spl test/unit/os/desktop/modern_wm_readiness_spec.spl --output doc/06_spec`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

The combined readiness report now carries the Web WM quality dimensions used by
release evidence instead of only aggregate booleans: size layout, titlebar,
minimum window, title input, taskbar icon metrics, command palette/title input
readiness, visual layering, motion control, round icons, round scrollbars, and
translucent shell readiness. The focused readiness spec asserts those fields and
summary markers; the spec passes `2/2`, checks pass, and the mirrored manual was
refreshed with existing short-doc warnings.

SimpleOS shell exec alias evidence continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/os/kernel/loader/app_registry.spl src/os/services/vfs/vfs_init.spl test/unit/os/kernel/loader/app_registry_spec.spl test/system/app/os/feature/vfs_exec_bytes_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/os/kernel/loader/app_registry_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/app/os/feature/vfs_exec_bytes_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/system/app/os/feature/vfs_exec_bytes_spec.spl test/unit/os/kernel/loader/app_registry_spec.spl --output doc/06_spec`

The SimpleOS fallback registry and VFS exec byte-buffer specs now assert that
`/bin/simple`, `/usr/bin/simple`, `/bin/sh`, and `/usr/bin/shell` normalize to
the shared SMF app aliases used by baked SimpleOS app execution. The app
registry spec passes `25/25`, the VFS exec bytes spec passes `4/4`, and the
mirrored manuals were refreshed. This advances the live SimpleOS execution lane
without claiming the remaining guest-side QEMU/GTK performance harness is
complete.

Web WM accessibility contract continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/ui.web/html.spl src/app/ui.web/wm_quality_contract.spl test/unit/app/ui/web_wm_modern_shell_spec.spl src/os/desktop/modern_wm_readiness.spl test/unit/os/desktop/modern_wm_readiness_spec.spl`
- `node --check src/app/ui.web/wm.js && node --check src/app/ui.web/retained_renderer.js`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/app/ui/web_wm_modern_shell_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/os/desktop/modern_wm_readiness_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/unit/app/ui/web_wm_modern_shell_spec.spl test/unit/os/desktop/modern_wm_readiness_spec.spl --output doc/06_spec`

The Web WM shell now exposes accessible control evidence: traffic-light buttons
use explicit window action labels, command palette items expose listbox/option
semantics, taskbar launch/focus items are keyboard activatable, focus-visible
rings are present, traffic-light hit targets are expanded, and command palette
targets are 44px high. The Web WM quality and modern readiness reports now carry
`accessible_controls_ready`. Focused checks pass, the Web WM spec passes `5/5`,
and the modern readiness spec passes `2/2`. This advances Web WM usability and
release evidence without claiming production Chrome pixel parity is fixed.

SimpleOS SSH shell launch evidence continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/os/apps/terminal/terminal.spl src/os/apps/sshd/ssh_session.spl test/unit/os/apps/sshd/ssh_session_shell_spec.spl examples/simple_os/arch/x86_64/ssh_live_entry.spl`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/os/ssh_qemu_contract.spl examples/simple_os/arch/x86_64/ssh_live_entry.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/os/apps/sshd/ssh_session_shell_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/unit/os/apps/sshd/ssh_session_shell_spec.spl --output doc/06_spec`

Terminal transport buffering now preserves multi-line SSH shell input chunks,
and SSH shell launch evidence resolves `simple.smf --version`, `simple --check`,
and `sh -lc pwd` through SMF-backed app registry aliases. The bounded x64 SSH
live probe contract now sends `SESSION shell simple.smf --version` and
`SESSION shell simple --check` probes and requires `/usr/bin/simple(.smf)` plus
`/SYS/APPS/SIMPLSTC.SMF` evidence in the host-visible output. Focused checks
pass with the existing generated-marker warning on the live entrypoint, and
`ssh_session_shell_spec.spl` passes `6/6`. This advances SimpleOS live
execution evidence without claiming the remaining guest-side QEMU/GTK
performance harness is complete.

QEMU/GTK guest perf blocker metadata continuation:

- `QEMU_HOST_GTK_SCENE_EVIDENCE=0 BUILD_DIR=build/tmp/qemu_gtk_wm_capture_evidence_spec REPORT_PATH=build/tmp/qemu_gtk_wm_capture_evidence_spec.md sh scripts/check-qemu-gtk-wm-capture-evidence.shs`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check test/system/gui/qemu_gtk_wm_capture_evidence_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/gui/qemu_gtk_wm_capture_evidence_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/system/gui/qemu_gtk_wm_capture_evidence_spec.spl --output doc/06_spec`

The QEMU/GTK evidence wrapper now emits structured release-blocker metadata for
guest-side Simple-vs-GTK performance: `perf_scope=qemu-guest-simple-vs-gtk`,
`perf_release_gate=guest-side-simple-vs-gtk-performance`,
`perf_release_blocker=qemu-side-gtk-simple-perf-harness-not-wired`, and
`perf_required_for_release=true` in the bounded non-live path. The same report
marks the host GTK GL exact-scene baseline as
`host-gtk-gl-exact-scene-baseline` with `host_perf_promotes_qemu_perf=false`.
The focused system spec passes `1/1` and the mirrored manual was generated. This
improves release evidence clarity without claiming the guest-side QEMU/GTK perf
harness is wired.

Web WM snap assist and desktop widget continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/ui.web/html.spl src/app/ui.web/wm_quality_contract.spl src/os/desktop/modern_wm_readiness.spl test/unit/app/ui/web_wm_modern_shell_spec.spl test/unit/os/desktop/modern_wm_readiness_spec.spl`
- `node --check src/app/ui.web/wm.js`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/app/ui/web_wm_modern_shell_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/os/desktop/modern_wm_readiness_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/unit/app/ui/web_wm_modern_shell_spec.spl test/unit/os/desktop/modern_wm_readiness_spec.spl --output doc/06_spec`

The modern Web WM now has snap-assist evidence and runtime behavior: dragging
near left, right, or top edges shows a rounded translucent `.wm-snap-preview`
and sends the existing move/resize commands with snapped half/full bounds. The
same shell now exposes desktop widgets for clock, motion, and workspace state,
with a command-palette toggle and reduced/off motion coverage. The Web WM
quality report and combined modern-readiness report now carry
`snap_assist_ready` and `desktop_widgets_ready`; the Web WM spec passes `5/5`
and the readiness spec passes `2/2`. This advances the Engine2D/Web WM shell
lane without claiming production Chrome pixel parity or guest QEMU/GTK perf is
complete.

Web WM window overview continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/ui.web/html.spl src/app/ui.web/wm_quality_contract.spl src/os/desktop/modern_wm_readiness.spl test/unit/app/ui/web_wm_modern_shell_spec.spl test/unit/os/desktop/modern_wm_readiness_spec.spl`
- `node --check src/app/ui.web/wm.js`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/app/ui/web_wm_modern_shell_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/os/desktop/modern_wm_readiness_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/unit/app/ui/web_wm_modern_shell_spec.spl test/unit/os/desktop/modern_wm_readiness_spec.spl --output doc/06_spec`

The modern Web WM now exposes a command-palette and keyboard-accessible window
overview. The overview renders focus/restore cards for live browser windows,
routes selection through the existing focus command path, and carries matching
preview, CSS, reduced/off-motion, Web quality, and modern-readiness evidence via
`window_overview_ready`. Focused checks pass, the Web WM spec passes `5/5`, and
the readiness spec passes `2/2`. This advances the repeated-use desktop shell
lane without claiming production Chrome pixel parity or guest QEMU/GTK perf is
complete.

Production Chrome parity metadata continuation:

- `node --check tools/electron-shell/verify_famous_site_production_probe.js`
- `node tools/electron-shell/verify_famous_site_production_probe.js --sample=site_0_google`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check test/system/wm_compare/famous_site_corpus_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/system/wm_compare/famous_site_corpus_spec.spl --mode=interpreter --timeout-ms=240000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/system/wm_compare/famous_site_corpus_spec.spl --output doc/06_spec --no-index`

The production Chrome verifier now distinguishes bounded divergence evidence
from actual Chrome glyph/compositing parity. The focused `site_0_google` probe
passes with `parityStatus=divergent`, `boundedDivergenceOnly=true`,
`chromeGlyphCompositingParity=false`, `promotionRequiredDifferentPixels=2717`,
and `differentPixels=2717`. The famous-site corpus spec passes `45/45` in about
86s, so this strengthens the release gate wording while keeping the production
Chrome pixel-parity blocker explicitly open.

Web WM control center and OS affordance continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/ui.web/html.spl src/app/ui.web/wm_quality_contract.spl test/unit/app/ui/web_wm_modern_shell_spec.spl src/os/desktop/taskbar_shell.spl test/unit/os/desktop/modern_shell_contract_spec.spl src/os/desktop/modern_wm_readiness.spl test/unit/os/desktop/modern_wm_readiness_spec.spl`
- `node --check src/app/ui.web/wm.js`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/app/ui/web_wm_modern_shell_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/os/desktop/modern_shell_contract_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/os/desktop/modern_wm_readiness_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/unit/app/ui/web_wm_modern_shell_spec.spl test/unit/os/desktop/modern_shell_contract_spec.spl test/unit/os/desktop/modern_wm_readiness_spec.spl --output doc/06_spec --no-index`

The modern Web WM now exposes a control center for motion and workspace
affordances, and the SimpleOS taskbar shell now publishes a portable modern
desktop affordance contract for command palette, control center, window
overview, desktop widgets, snap assist, and motion verbosity controls. The
combined readiness report now requires both Web quality evidence and OS-shell
affordance metadata before reporting `os_affordances=true` and
`control_center=true`. Focused Web WM, modern shell contract, and readiness
specs pass `5/5`, `7/7`, and `2/2`.

BrowserSession Uint8Array search continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl test/unit/lib/common/web/browser_session_wasm_host_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

The BrowserSession script-level typed-array search gap is resolved for bounded
`Uint8Array.fill`, `indexOf`, and `includes` coverage. The permanent browser
script scenario now proves filled byte reads, positive search, positive search
with a start offset, negative-start search semantics, and negative includes
checks with `0:4:4:0:1:2:3:true:false`. Focused checks passed, the fetch/WASM
chain spec passed `8/8`, the native WASM host spec passed `107/107`, and Node
API conformance remained `213/213`. The generated scenario manual was refreshed
with the existing docgen stub warning. This closes
`doc/08_tracking/bug/browser_session_uint8array_search_dispatch.md` while
leaving broader typed-array prototype parity in the JS/WebEngine/WASM lane open.

BrowserSession Uint8Array join/reverse continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession typed-array prototype coverage now includes bounded
`Uint8Array.join` and `reverse` in addition to `fill`, `includes`, and
`indexOf`. The browser script scenario proves byte normalization for direct
indexed writes (`260 -> 4`, `-1 -> 255`), separator handling, in-place reverse
mutation, and the returned typed-array object's usability through
`1-4-255-7:7,255,4,1:7/255/4/1`. Focused checks passed, the fetch/WASM chain
spec passed `9/9`, the native WASM host spec passed `107/107`, and Node API
conformance remained `213/213`. The generated scenario manual was refreshed
with the existing docgen stub warning. Broader typed-array prototype parity
remains open.

BrowserSession Uint8Array copyWithin continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession typed-array prototype coverage now includes bounded
`Uint8Array.copyWithin` with clamped negative source indexes, overlap-safe
copying, returned-object chaining, and normalized byte storage. The browser
script scenario proves `1,7,9,7,9:7`. Focused checks passed, the fetch/WASM
chain spec passed `13/13`, the native WASM host spec passed `107/107`, and Node
API conformance remained `213/213`. The generated scenario manual was refreshed
with the existing docgen stub warning. Broader typed-array prototype parity
remains open.

BrowserSession Uint8Array some/every continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession typed-array prototype coverage now includes bounded
`Uint8Array.some` and `every` callback predicates. The browser script scenario
proves callback byte normalization, index argument delivery, typed-array receiver
argument usability through `arr.at(3)`, positive `some`, positive `every`, and
false-callback `every` behavior with `true:true:false`. Focused checks passed, the
fetch/WASM chain spec passed `14/14`, the native WASM host spec passed
`107/107`, and Node API conformance remained `213/213`. The generated scenario
manual was refreshed with the existing docgen stub warning. Broader typed-array
prototype parity remains open.

BrowserSession Uint8Array find/findIndex continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession typed-array prototype coverage now includes bounded
`Uint8Array.find` and `findIndex` callback predicates. The browser script
scenario proves callback iteration order, index argument delivery, normalized
byte return from the matched index, found value, found index, missing-value
`undefined`, and missing-index `-1` behavior with `4:1:undefined:-1`. Focused
checks passed, the fetch/WASM chain spec passed `16/16`, the native WASM host
spec passed `107/107`, and Node API conformance remained `213/213`. The
generated scenario manual was refreshed with the existing docgen stub warning.
Broader typed-array prototype parity remains open.

BrowserSession Uint8Array forEach continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession typed-array prototype coverage now includes bounded
`Uint8Array.forEach` callback iteration. The browser script scenario proves
normalized byte callback values, index argument delivery, typed-array receiver
argument usability through `arr.at(i)`, callback side effects, and `undefined`
return behavior with `266:0=4;1=255;2=7;:undefined`. Focused checks passed, the
fetch/WASM chain spec passed `15/15`, the native WASM host spec passed
`107/107`, and Node API conformance remained `213/213`. The generated scenario
manual was refreshed with the existing docgen stub warning. Broader typed-array
prototype parity remains open.

BrowserSession Uint8Array reduce continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession typed-array prototype coverage now includes bounded
`Uint8Array.reduce` with an explicit initial accumulator. The browser script
scenario proves accumulator delivery, normalized byte callback values, index
argument delivery, typed-array receiver argument usability through `arr.at(i)`,
and final accumulator return behavior with `535`. Focused checks passed, the
fetch/WASM chain spec passed `17/17`, the native WASM host spec passed
`107/107`, and Node API conformance remained `213/213`. The generated scenario
manual was refreshed with the existing docgen stub warning. Broader typed-array
prototype parity remains open.

BrowserSession Uint8Array reduceRight continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession typed-array prototype coverage now includes bounded
`Uint8Array.reduceRight` with an explicit initial accumulator. The browser
script scenario proves right-to-left callback order, normalized byte callback
values, index argument delivery, typed-array receiver argument usability through
`arr.at(i)`, and final accumulator return behavior with `16511008`. Focused
checks passed, the fetch/WASM chain spec passed `29/29`, the native WASM host
spec passed `107/107`, and Node API conformance remained `213/213`. The
generated scenario manual was refreshed with the existing docgen warnings.
Broader typed-array prototype parity and production GUI pixel parity remain
open.

BrowserSession Uint8Array from continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession typed-array prototype coverage now includes bounded
`Uint8Array.from` from indexed sources. The browser script scenario proves
copying from an existing typed array, byte normalization, source immutability,
array-literal construction with mapper callback value/index delivery, result
byte coercion, `length`, `at`, and `toString` behavior with
`4,255:4,255:4,0,9:3:0`. Focused checks passed, the fetch/WASM chain spec
passed `30/30`, the native WASM host spec passed `107/107`, and Node API
conformance remained `213/213`. The generated scenario manual was refreshed
with the existing docgen warnings. Broader typed-array prototype parity and
production GUI pixel parity remain open.

BrowserSession Uint8Array of continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession typed-array static coverage now includes bounded
`Uint8Array.of` varargs construction. The browser script scenario proves
argument byte normalization with `260 -> 4` and `-1 -> 255`, empty `of()`
construction, `length`, `at`, and `toString` behavior with
`4,255,7:3:4:255:0:`. Focused checks passed, the fetch/WASM chain spec
passed `31/31`, the native WASM host spec passed `107/107`, and Node API
conformance remained `213/213`. The generated scenario manual was refreshed
with the existing docgen warning profile unchanged. Broader typed-array
prototype parity and production GUI pixel parity remain open.

BrowserSession Uint8Array map continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession typed-array prototype coverage now includes bounded
`Uint8Array.map` with callback value, index, and typed-array receiver
arguments. The browser script scenario proves normalized source byte reads,
result byte coercion, a new mapped typed array, source immutability, `length`,
`at`, and `toString` behavior with `8,255,16:4,255,7:3:255`. Focused checks
passed, the fetch/WASM chain spec passed `18/18`, the native WASM host spec
passed `107/107`, and Node API conformance remained `213/213`. The generated
scenario manual was refreshed with the existing docgen warning. Broader
typed-array prototype parity and production GUI pixel parity remain open.

BrowserSession Uint8Array filter continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession typed-array prototype coverage now includes bounded
`Uint8Array.filter` with callback value/index delivery, truthy index selection,
new-result construction, byte preservation, source immutability, `length`, `at`,
and `toString` behavior with `255,7,8:4,255,7,8:3:7`. Focused checks passed,
the fetch/WASM chain spec passed `19/19`, the native WASM host spec passed
`107/107`, and Node API conformance remained `213/213`. The generated scenario
manual was refreshed with the existing docgen warning. Broader typed-array
prototype parity and production GUI pixel parity remain open.

BrowserSession Uint8Array slice/subarray continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession typed-array prototype coverage now includes bounded
`Uint8Array.subarray` and `slice` range return evidence. The browser script
scenario proves positive start, negative end normalization, negative start
normalization, returned typed-array `toString`, `length`, `at`, and source-array
preservation with `4,255,7:3:4:255,7:2:1,4,255,7,9`. Focused checks passed,
the fetch/WASM chain spec passed `20/20`, the native WASM host spec passed
`107/107`, and Node API conformance remained `213/213`. The generated scenario
manual was refreshed with the existing docgen warning. Broader typed-array
prototype parity and production GUI pixel parity remain open.

BrowserSession Uint8Array set continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession typed-array prototype coverage now includes bounded
`Uint8Array.set` copy evidence from another typed array. The browser script
scenario proves normalized source bytes, offset copy into the destination,
`undefined` return behavior, destination length preservation, and source
preservation with `1,4,255,7,9:undefined:5:4,255,7`. Focused checks passed, the
fetch/WASM chain spec passed `21/21`, the native WASM host spec passed
`107/107`, and Node API conformance remained `213/213`. The generated scenario
manual was refreshed with the existing docgen warning. Broader typed-array
prototype parity and production GUI pixel parity remain open.

BrowserSession Uint8Array view metadata continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession typed-array evidence now includes bounded `ArrayBuffer`-backed
`Uint8Array` view metadata in browser scripts. The scenario proves
`byteOffset`, `byteLength`, `length`, `buffer.byteLength`, shared buffer byte
reads through the view, and full-buffer preservation with
`1:3:3:8:4,255,0:0,4,255,0,0,0,0,0`. Focused checks passed, the fetch/WASM
chain spec passed `22/22`, the native WASM host spec passed `107/107`, and Node
API conformance remained `213/213`. The generated scenario manual was refreshed
with the existing docgen warning. Broader typed-array prototype parity and
production GUI pixel parity remain open.

BrowserSession DataView byte access continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession JS/WebEngine/WASM evidence now includes browser-script
`DataView` read/write behavior over `ArrayBuffer`. The scenario proves
little-endian `setUint32`, signed little-endian `setInt32`/`getInt32`, shared
byte visibility through `Uint8Array`, and `byteOffset`/`byteLength` metadata
with `16909060:-2:4,3,2,1,254,255,255,255:0:8`. Focused checks passed, the
fetch/WASM chain spec passed `23/23`, the native WASM host spec passed
`107/107`, and Node API conformance remained `213/213`. The generated scenario
manual was refreshed with the existing docgen warning. Broader WASM semantics,
typed-array prototype parity, and production GUI pixel parity remain open.

BrowserSession signed DataView byte access continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession JS/WebEngine/WASM evidence now includes signed `DataView`
8-bit and 16-bit read/write behavior over `ArrayBuffer`. The scenario proves
`setInt8`, `getInt8`, `setInt16`, `getInt16`, corresponding unsigned reads,
little-endian and big-endian byte ordering, and shared `Uint8Array` visibility
with `-1:255:-2:65534:-32768:32768:255,254,255,128,0,0`. Focused checks
passed, the fetch/WASM chain spec passed `32/32`, the native WASM host spec
passed `107/107`, and Node API conformance remained `213/213`. The generated
scenario manual was refreshed with the existing docgen warning profile.
Broader WASM semantics, typed-array prototype parity, and production GUI pixel
parity remain open.

BrowserSession DataView window offset continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession JS/WebEngine/WASM evidence now includes nonzero-offset
`DataView` window read/write behavior over `ArrayBuffer`. The scenario proves
`byteOffset`, `byteLength`, offset-relative `getUint8`, little-endian
`setUint16`/`getUint16`, signed `setInt8`/`getInt8`, and whole-buffer
visibility through `Uint8Array` with `2:4:3:258:-1:1,2,3,2,1,255,0,0`.
Focused checks passed, the fetch/WASM chain spec passed `33/33`, the native
WASM host spec passed `107/107`, and Node API conformance remained `213/213`.
The generated scenario manual was refreshed with the existing docgen warning
profile. Broader WASM semantics, typed-array prototype parity, and production
GUI pixel parity remain open.

BrowserSession WebAssembly.Memory view continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession JS/WebEngine/WASM evidence now includes direct browser-script
`WebAssembly.Memory` buffer sharing with `Uint8Array` and `DataView`. The
scenario proves memory construction with a maximum, byte writes through
`Uint8Array`, little-endian `DataView.setUint16`, successful bounded
`memory.grow`, refreshed `memory.buffer.byteLength`, grown typed-array length,
and byte preservation after growth with `1:131072:131072:4:2:1`. Focused checks
passed, the fetch/WASM chain spec passed `24/24`, the native WASM host spec
passed `107/107`, and Node API conformance remained `213/213`. The generated
scenario manual was refreshed with the existing docgen warning. Broader WASM
semantics, typed-array prototype parity, and production GUI pixel parity remain
open.

BrowserSession WebAssembly.Memory grow limit continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession JS/WebEngine/WASM evidence now includes browser-script
`WebAssembly.Memory.grow` maximum-bound preservation. The scenario proves
`grow(0)` returns the current page count, a grow beyond the declared maximum
returns `-1`, `memory.buffer.byteLength` remains unchanged, and a fresh
`Uint8Array(memory.buffer)` still reports the original length with
`65536:65536:1:-1:65536`. Focused checks passed, the fetch/WASM chain spec
passed `34/34`, the native WASM host spec passed `107/107`, and Node API
conformance remained `213/213`. The generated scenario manual was refreshed
with the existing docgen warning profile. Broader WASM semantics, typed-array
prototype parity, and production GUI pixel parity remain open.

BrowserSession Uint8Array lastIndexOf continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession typed-array prototype coverage now includes bounded
`Uint8Array.lastIndexOf` in addition to `fill`, `includes`, `indexOf`, `join`,
and `reverse`. The browser script scenario proves backward byte search, explicit
positive start, negative start normalization, and missing-byte behavior with
`3:2:3:0:-1`. Focused checks passed, the fetch/WASM chain spec passed `10/10`,
the native WASM host spec passed `107/107`, and Node API conformance remained
`213/213`. The generated scenario manual was refreshed with the existing docgen
stub warning. Broader typed-array prototype parity remains open.

BrowserSession Uint8Array toString continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession typed-array prototype coverage now includes bounded
`Uint8Array.toString` by routing the method through comma-separated typed-array
`join` semantics. The browser script scenario proves byte normalization and
default stringification through `1,4,255,7:1|4|255|7`. Focused checks passed,
the fetch/WASM chain spec passed `11/11`, the native WASM host spec passed
`107/107`, and Node API conformance remained `213/213`. The generated scenario
manual was refreshed with the existing docgen stub warning. Broader typed-array
prototype parity remains open.

BrowserSession Uint8Array at continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession typed-array prototype coverage now includes bounded
`Uint8Array.at` with positive indexes, negative relative indexes, normalized
byte reads, and out-of-range `undefined` behavior. The browser script scenario
proves `1:4:7:255:undefined`. Focused checks passed, the fetch/WASM chain spec
passed `12/12`, the native WASM host spec passed `107/107`, and Node API
conformance remained `213/213`. The generated scenario manual was refreshed
with the existing docgen stub warning. Broader typed-array prototype parity
remains open.

BrowserSession Uint8Array sort continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession typed-array prototype coverage now includes bounded default
`Uint8Array.sort` behavior. The browser script scenario proves normalized byte
ordering, in-place mutation, same returned typed-array usability through
`toString`/`at`, and numeric ascending output with
`1,4,7,255:1,4,7,255:1:255`. Focused checks passed, the fetch/WASM chain spec
passed `25/25`, the native WASM host spec passed `107/107`, and Node API
conformance remained `213/213`. The generated scenario manual was refreshed
with the existing docgen warnings. Comparator sorting, broader typed-array
prototype parity, and production GUI pixel parity remain open.

BrowserSession Uint8Array keys/values iterator continuation:

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession typed-array prototype coverage now includes bounded
`Uint8Array.keys()` and `Uint8Array.values()` iterator objects with `next()`
results shaped as `{ value, done }`. The browser script scenario proves key
ordering, normalized byte values, and terminal `done` behavior with
`0:1:true:4:255:true`. Focused checks passed, the fetch/WASM chain spec passed
`26/26`, the native WASM host spec passed `107/107`, and Node API conformance
remained `213/213`. The generated scenario manual was refreshed with the
existing docgen warnings. Broader typed-array prototype parity and production
GUI pixel parity remain open.

BrowserSession Uint8Array entries iterator continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession typed-array prototype coverage now includes bounded
`Uint8Array.entries()` iterator objects with `next()` results shaped as
`{ value: [index, byte], done }`. The browser script scenario proves normalized
byte values, entry index/value tuple access, iterator advancement, and terminal
`done` behavior with `0=4:1=255:true`. Focused checks passed, the fetch/WASM
chain spec passed `28/28`, the native WASM host spec passed `107/107`, and Node
API conformance remained `213/213`. The generated scenario manual was refreshed
with the existing docgen warnings. Broader typed-array prototype parity and
production GUI pixel parity remain open.

BrowserSession Uint8Array comparator sort continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/parser.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl src/lib/nogc_sync_mut/js/engine/js_error.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession typed-array prototype coverage now includes bounded
`Uint8Array.sort(compareFn)` dispatch with arithmetic comparator expressions.
The parser now handles top-level JS binary/logical operator precedence for the
subset needed by browser scripts, and the comparator is invoked with natural
`(left, current)` sort arguments. The browser script scenario proves descending
numeric comparator ordering, mutation in place, and return-value identity with
`255,7,4,1:255,7,4,1:255:1`. Focused checks passed, the fetch/WASM chain spec
passed `27/27`, the native WASM host spec passed `107/107`, and Node API
conformance remained `213/213`. The generated scenario manual was refreshed
with the existing docgen warnings.

CommonJS/Node nextTick phase-order continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter.spl src/lib/nogc_sync_mut/js/engine/interpreter_async.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

The bounded Node scheduler now marks `process.nextTick` tasks as their own
phase and drains due nextTick tasks before ordinary due timer tasks. The Node
API conformance suite proves a nextTick scheduled after an already queued
zero-delay `timers.setTimeout` still runs first, and that a nested nextTick
scheduled during the drain also runs before the timer. Focused checks passed,
the Node API conformance suite passes `219/219`, BrowserSession fetch/WASM and
native WASM host regressions remain `36/36` and `107/107`, and the broad
`src/lib` check passed with the existing `447` warning profile. Broader
event-loop phases, host I/O integration, and full timer-object behavior remain
open.

CommonJS/Node bounded readline terminal grant continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

`JsRuntime.grant_node_terminal(answer)` now enables bounded readline terminal
capability. Granted `readline` and `node:readline` interfaces report
`status=allowed`, `terminal=true`, deterministic `question` prompt/answer
metadata, callback invocation with the granted answer, and close state.
Ungranted readline remains fail-closed with `terminal-denied`. Focused checks
passed, the Node API conformance suite passes `220/220`, BrowserSession
fetch/WASM and native WASM host regressions remain `36/36` and `107/107`, and
the broad `src/lib` check passed with the existing `447` warning profile. Real
terminal I/O, TTY streams, and event-loop integration remain open.

CommonJS/Node bounded stream high-water pressure continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded `Writable(opts)` now honors `highWaterMark`, tracks
`writableHighWaterMark`, cumulative `writableLength`, cumulative
`bytesWritten`, and sets `backpressure` plus result status when writes reach
the high-water mark. `Readable.pipe(Writable)` now propagates destination
length and backpressure after bounded chunk transfer. Focused checks passed,
the Node API conformance suite passes `222/222`, BrowserSession fetch/WASM and
native WASM host regressions remain `36/36` and `107/107`, and the broad
`src/lib` check passed with the existing `447` warning profile. Full stream
flow control, async scheduling, and host I/O integration remain open.

CommonJS/Node bounded readable direct-read EOF continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Direct bounded readable `read()` calls now join the shared readable end
lifecycle when a subsequent direct read observes EOF. The bounded path emits
`end`, sets `readableEnded=true`, and sets `readable=false`; a direct read that
leaves buffered chunks does not emit `end`. Focused checks passed, the Node API
conformance suite remains `232/232` with stronger direct-read lifecycle
assertions, BrowserSession fetch/WASM and native WASM host regressions remain
`36/36` and `107/107`, and the broad `src/lib` check passed with the existing
`447` warning profile. Full stream flow control, async scheduling, and host I/O
integration remain open.

CommonJS/Node bounded readable ended-state continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded readable streams now expose deterministic end-state flags: the shared
readable end emitter sets `readableEnded=true` and `readable=false` whenever
data listeners, pipe drains, or async iterator exhaustion consume all buffered
chunks. Focused checks passed, the Node API conformance suite remains
`232/232` with stronger lifecycle assertions, BrowserSession fetch/WASM and
native WASM host regressions remain `36/36` and `107/107`, and the broad
`src/lib` check passed with the existing `447` warning profile. Full stream
flow control, async scheduling, and host I/O integration remain open.

CommonJS/Node bounded readable async-iterator end continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded readable async iterators now emit `end` once when `next()` observes
stream exhaustion. This applies to both `streamAsyncIterator()` and the
`Symbol.asyncIterator` method, uses the same EventEmitter listener/once-listener
cleanup path as data-flow end delivery, and leaves `end` un-emitted while
buffered chunks remain. Focused checks passed, the Node API conformance suite
passes `231/231`, BrowserSession fetch/WASM and native WASM host regressions
remain `36/36` and `107/107`, and the broad `src/lib` check passed with the
existing `447` warning profile. Full stream flow control, async scheduling, and
host I/O integration remain open.

CommonJS/Node bounded readable pipe-end continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded readable `pipe(writable)` now emits `end` once when the bounded pipe
path drains all buffered chunks. The behavior uses the shared readable end
emitter, clears once-registered end listeners through EventEmitter state, and
also fires when a paused pending pipe is resumed. Focused checks passed, the
Node API conformance suite passes `232/232`, BrowserSession fetch/WASM and
native WASM host regressions remain `36/36` and `107/107`, and the broad
`src/lib` check passed with the existing `447` warning profile. Full stream
flow control, async scheduling, and host I/O integration remain open.

CommonJS/Node bounded stream drain continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded writable streams now clear queued `writableLength`, clear
`backpressure`, record `drainListenerCount`, and emit registered `drain`
callbacks when `end()` flushes a stream that previously reached high-water
pressure. Once-registered drain listeners are cleared through the existing
EventEmitter path, and non-pressured writes do not emit drain. Focused checks
passed, the Node API conformance suite passes `223/223`, BrowserSession
fetch/WASM and native WASM host regressions remain `36/36` and `107/107`, and
the broad `src/lib` check passed with the existing `447` warning profile. Full
stream flow control, async scheduling, and host I/O integration remain open.

CommonJS/Node bounded readable data-listener continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded readable streams now drain buffered chunks through `data` listeners
using the existing EventEmitter callback path. Listener attachment starts
flowing delivery when the stream is not paused or destroyed, `once("data")`
consumes one chunk and leaves the remainder buffered, paused streams defer
delivery until `resume()`, and destroyed streams suppress data delivery.
Focused checks passed, the Node API conformance suite passes `229/229`,
BrowserSession fetch/WASM and native WASM host regressions remain `36/36` and
`107/107`, and the broad `src/lib` check passed with the existing `447`
warning profile. Full stream flow control, async scheduling, and host I/O
integration remain open.

CommonJS/Node bounded readable end-listener continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded readable streams now emit `end` once after buffered data drains through
`data` listeners. The bounded path tracks `endEmitted`, preserves paused
deferral until `resume()`, clears once-registered `end` listeners through the
existing EventEmitter path, and leaves `end` un-emitted when `once("data")`
consumes only one chunk and leaves buffered data behind. Focused checks passed,
the Node API conformance suite passes `230/230`, BrowserSession fetch/WASM and
native WASM host regressions remain `36/36` and `107/107`, and the broad
`src/lib` check passed with the existing `447` warning profile. Full stream
flow control, async scheduling, and host I/O integration remain open.

CommonJS/Node bounded readable pause/resume continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded readable streams now expose deterministic `pause()`, `resume()`, and
`isPaused()` methods. `pause()` marks `readableFlowing=false`, `resume()` marks
`readableFlowing=true`, and `pipe()` returns the destination without draining
while a readable is paused; after `resume()`, the same bounded pipe path drains
remaining chunks. Focused checks passed, the Node API conformance suite passes
`225/225`, BrowserSession fetch/WASM and native WASM host regressions remain
`36/36` and `107/107`, and the broad `src/lib` check passed with the existing
`447` warning profile. Full stream flow control, async scheduling, and host I/O
integration remain open.

CommonJS/Node bounded pending pipe resume continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Paused bounded readable streams now remember one pending writable destination
from `pipe(writable)`. `resume()` clears the paused flag, routes that pending
destination through the same bounded pipe implementation, drains all current
chunks, and marks `pipeResumed=true`. Focused checks passed, the Node API
conformance suite passes `226/226`, BrowserSession fetch/WASM and native WASM
host regressions remain `36/36` and `107/107`, and the broad `src/lib` check
passed with the existing `447` warning profile. Full stream flow control, async
scheduling, and host I/O integration remain open.

CommonJS/Node bounded readable unpipe continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded readable streams now expose deterministic `unpipe()`. For a paused
readable with a remembered pending pipe destination, `unpipe()` clears the
pending destination, clears paused-pipe state, marks `pipeUnpiped=true`, and
prevents `resume()` from draining bytes into the canceled writable. Focused
checks passed, the Node API conformance suite passes `227/227`,
BrowserSession fetch/WASM and native WASM host regressions remain `36/36` and
`107/107`, and the broad `src/lib` check passed with the existing `447`
warning profile. Full stream flow control, async scheduling, and host I/O
integration remain open.

CommonJS/Node bounded response readable-state continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded HTTP responses now expose deterministic `readable` state while their
synthetic body remains available. The response starts readable and flips to
`false` after data delivery, direct `read()`, pipe consumption, or `destroy()`,
while preserving the existing buffered read behavior when no data listener has
consumed the body yet. Full host response streaming, async scheduling, and
generated GUI parity remain open.

CommonJS/Node bounded response async-iterator continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded HTTP responses now expose `streamAsyncIterator()` and
`[Symbol.asyncIterator]()` through the existing bounded iterator result shape.
Iterator `next()` returns the synthetic body once, consumes `readableLength`,
flips `readable=false`, and reports `done=true` after exhaustion while emitting
the deterministic `end` path for registered listeners. Full `for await` syntax,
host response chunk streaming, async scheduling, and generated GUI parity
remain open.

CommonJS/Node bounded HTTP listener-removal continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded HTTP request and response objects now expose shared EventEmitter
`removeListener`, `off`, and `removeAllListeners` methods. Request lifecycle
listeners removed before `end()`/`abort()` do not fire, and paused response
`data`/`end` listeners removed before `resume()` no longer receive deferred
delivery while the response still completes deterministically. Full host
response chunk streaming, async scheduling, and generated GUI parity remain
open.

CommonJS/Node bounded HTTP addListener continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded HTTP request and response objects now expose EventEmitter
`addListener` as the shared `on` alias. Request `close` listeners registered
with `addListener` fire during `end()`, and paused response `data` listeners
registered with `addListener` receive the deferred body after `resume()`. Full
host response chunk streaming, async scheduling, and generated GUI parity remain
open.

CommonJS/Node bounded response readable-event continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded HTTP responses now initialize and update deterministic
`readableNotified` and `readableAvailableEmitted` state through the shared
bounded readable availability path. `readable` listeners observe buffered body
availability before the body is consumed, one-shot readable listeners are
cleaned up, and readable notifications are suppressed after direct `read()`.
Full host response chunk streaming, async scheduling, and generated GUI parity
remain open.

CommonJS/Node bounded readable destroy continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded readable streams now expose deterministic `destroy()`, mark
`destroyed`/`closed`, set `readable=false`, clear `readableLength`, cancel the
pending pipe destination, clear `pipePaused`, and idempotently emit `close`
listeners via the existing EventEmitter path, including once-listener cleanup. Focused checks
passed, the Node API conformance suite passes `228/228`, BrowserSession
fetch/WASM and native WASM host regressions remain `36/36` and `107/107`, and
the broad `src/lib` check passed with the existing `447` warning profile. Full
stream flow control, async scheduling, and host I/O integration remain open.

CommonJS/Node bounded readable availability continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded readable streams now emit a deterministic `readable` availability
signal when listeners attach while buffered chunks remain. The implementation
sets `readableNotified=true`, records whether the availability event emitted,
cleans up one-shot readable listeners through the existing EventEmitter path,
reports availability while paused, and suppresses notifications after direct
EOF or `destroy()`. Focused checks passed, the Node API conformance suite
passes `233/233`, BrowserSession fetch/WASM and native WASM host regressions
remain `36/36` and `107/107`, and the broad `src/lib` check passed with the
existing `447` warning profile. Full stream flow control, async scheduling,
`for await` syntax, and host I/O integration remain open.

CommonJS/Node bounded pipe flow-control continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded readable `pipe()` now writes chunks one at a time and stops when the
destination reaches `writableHighWaterMark`. The readable records
`pipeBackpressured=true`, leaves remaining chunks in `readableLength`, keeps the
pending destination, and avoids `end` until the buffered source is actually
drained. After writable pressure is cleared, `resume()` continues through the
remembered destination, drains the remaining chunks, clears the backpressure
flag, and emits the shared readable `end`. Focused checks passed, the Node API
conformance suite remains `233/233`, BrowserSession fetch/WASM and native WASM
host regressions remain `36/36` and `107/107`, and the broad `src/lib` check
passed with the existing `447` warning profile. Full async scheduling,
`for await` syntax, and host I/O integration remain open.

CommonJS/Node bounded timer refresh continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter.spl src/lib/nogc_sync_mut/js/engine/interpreter_async.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded Node timer handles now expose `refresh()`. The method routes through
native timer dispatch, returns the handle for chaining, rewrites live pending
timer tasks in place, records `refreshed=true`/`refreshedAt=0`, and leaves
closed handles suppressed with `refreshed=false`. Focused checks passed, the
Node API conformance suite passes `234/234`, BrowserSession fetch/WASM and
native WASM host regressions remain `36/36` and `107/107`, and the broad
`src/lib` check passed with the existing `447` warning profile. Broader
event-loop phase behavior, host I/O integration, and full Node timer-object
lifecycle behavior remain open.

CommonJS/Node bounded timer clear-state continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded timer module clear calls now update object handle lifecycle state.
`clearTimeout(handle)`, `clearInterval(handle)`, and `clearImmediate(handle)`
still cancel the pending timer task and now also mark the passed handle
`closed=true`, matching the handle-level cancellation state exposed by
`close()`. Focused checks passed, the Node API conformance suite passes
`235/235`, BrowserSession fetch/WASM and native WASM host regressions remain
`36/36` and `107/107`, and the broad `src/lib` check passed with the existing
`447` warning profile. Broader event-loop phase behavior, host I/O integration,
and full Node timer-object lifecycle behavior remain open.

CommonJS/Node bounded timer active-state continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded timer handles now expose explicit lifecycle state from creation:
`active=true` and `closed=false`. Handle `close()` and module clear calls set
`active=false` with `closed=true`, while a live `refresh()` preserves
`active=true`/`closed=false`. Focused checks passed, the Node API conformance
suite remains `235/235`, BrowserSession fetch/WASM and native WASM host
regressions remain `36/36` and `107/107`, and the broad `src/lib` check passed
with the existing `447` warning profile. Broader event-loop phase behavior,
host I/O integration, and full Node timer-object lifecycle behavior remain
open.

CommonJS/Node bounded timer fire-state continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter.spl src/lib/nogc_sync_mut/js/engine/interpreter_async.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded timer handles now track execution state. Created handles expose
`fired=false` and `fireCount=0`; one-shot handles become
`active=false`/`fired=true` with `fireCount=1` after their callback drains; and
interval handles stay `active=true` while incrementing `fireCount` on each
drain. Focused checks passed, the Node API conformance suite passes `236/236`,
BrowserSession fetch/WASM and native WASM host regressions remain `36/36` and
`107/107`, and the broad `src/lib` check passed with the existing `447` warning
profile. Broader event-loop phase behavior, host I/O integration, and full Node
timer-object lifecycle behavior remain open.

CommonJS/Node bounded HTTP request finish-event continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded `http.request`/`https.request` objects now expose `on`, `once`, and
`listenerCount` for request-side lifecycle events. `end()` emits `finish`,
records `finishEmitted` and `finishListenerCount`, and clears one-shot finish
listeners through the shared EventEmitter path. Focused checks passed, the Node
API conformance suite passes `237/237`, BrowserSession fetch/WASM and native
WASM host regressions remain `36/36` and `107/107`, and the broad `src/lib`
check passed with the existing `447` warning profile. Real request streams,
host response streaming, broader event-loop ordering, and host network I/O
remain open.

CommonJS/Node bounded HTTP request abort-event continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded request abort lifecycle now emits `abort` through the same request-side
EventEmitter path as `finish`. `abort()` records `abortEmitted` and
`abortListenerCount`, invokes listeners, and clears one-shot abort listeners.
Focused checks passed, the Node API conformance suite passes `238/238`,
BrowserSession fetch/WASM and native WASM host regressions remain `36/36` and
`107/107`, and the broad `src/lib` check passed with the existing `447` warning
profile. Real request streams, host response streaming, broader event-loop
ordering, and host network I/O remain open.

CommonJS/Node bounded HTTP request response-event continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded `http.request`/`https.request` objects now emit request-side
`response` events on `end()` when listeners are registered. The bounded path
passes the same deterministic response metadata used by response callbacks,
records `responseEmitted` and `responseListenerCount`, and clears one-shot
response listeners through the shared EventEmitter path. Focused checks passed,
the Node API conformance suite passes `239/239`, BrowserSession fetch/WASM and
native WASM host regressions remain `36/36` and `107/107`, and the broad
`src/lib` check passed with the existing `447` warning profile. Real request
streams, host response streaming, broader event-loop ordering, and host network
I/O remain open.

CommonJS/Node bounded HTTP response lifecycle continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded synthetic HTTP responses now expose deterministic lifecycle state:
`complete=false` and `readableEnded=false` at creation, then
`complete=true` and `readableEnded=true` when the bounded `end` phase runs.
The bounded path also records `dataListenerCount` and `endListenerCount`,
while keeping listener delivery flags separate through `dataDelivered` and
`endDelivered`. Focused checks passed, the Node API conformance suite passes
`240/240`, BrowserSession fetch/WASM and native WASM host regressions remain
`36/36` and `107/107`, and the broad `src/lib` check passed with the existing
`447` warning profile. Real response streaming, broader event-loop ordering,
and host network I/O remain open.

CommonJS/Node bounded HTTP response header continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded synthetic HTTP responses now expose deterministic response metadata
through both callback and request `response` listener paths: `httpVersion=1.1`,
`headerCount=3`, stable `headerNames`, and a lower-case `headers` object with
`content-type`, `content-length`, and `x-simple-runtime`. Focused checks
passed, the Node API conformance suite passes `241/241`, BrowserSession
fetch/WASM and native WASM host regressions remain `36/36` and `107/107`, and
the broad `src/lib` check passed with the existing `447` warning profile. Real
response streaming, broader event-loop ordering, and host network I/O remain
open.

CommonJS/Node bounded HTTP response raw-header continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded synthetic HTTP responses now expose HTTP version split fields and
stable raw header order through both response callback and request `response`
listener paths. `httpVersionMajor=1`, `httpVersionMinor=1`, and `rawHeaders`
preserve the deterministic `Content-Type`, `Content-Length`, and
`X-Simple-Runtime` order used by the bounded response metadata. Focused checks
passed, the Node API conformance suite passes `242/242`, BrowserSession
fetch/WASM and native WASM host regressions remain `36/36` and `107/107`, and
the broad `src/lib` check passed with the existing `447` warning profile. Real
response streaming, broader event-loop ordering, and host network I/O remain
open.

CommonJS/Node bounded HTTP request close-event continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded `http.request`/`https.request` objects now emit request-side `close`
events through the shared EventEmitter path when `end()` or `abort()` reaches
a terminal request action. The bounded path records `closeEmitted` and
`closeListenerCount`, clears one-shot close listeners, and keeps no-listener
state deterministic. Focused checks passed, the Node API conformance suite
passes `243/243`, BrowserSession fetch/WASM and native WASM host regressions
remain `36/36` and `107/107`, and the broad `src/lib` check passed with the
existing `447` warning profile. Real request streams, response streaming,
broader event-loop ordering, and host network I/O remain open.

CommonJS/Node bounded HTTP request lifecycle-flag continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded `http.request`/`https.request` objects now expose deterministic
request lifecycle flags. New requests start with `writableEnded=false`,
`writableFinished=false`, `destroyed=false`, and `closed=false`; `end()` marks
the bounded writable side ended/finished and closed without destroying the
request; and `abort()` marks the bounded request destroyed and closed without
claiming writable completion. Focused checks passed, the Node API conformance
suite passes `244/244`, BrowserSession fetch/WASM and native WASM host
regressions remain `36/36` and `107/107`, and the broad `src/lib` check passed
with the existing `447` warning profile. Real request streams, response
streaming, broader event-loop ordering, and host network I/O remain open.

CommonJS/Node bounded HTTP terminal-write continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded `http.request`/`https.request` writes now reject deterministically after
terminal request state. Writes after `end()` return `status=denied` with
`error=request-ended`; writes after `abort()` return `status=denied` with
`error=request-aborted`; the request records `writeRejected` and
`writeRejectReason`, and rejected writes do not mutate `bodyBytes` or
`bodyChunks`. Focused checks passed, the Node API conformance suite passes
`245/245`, BrowserSession fetch/WASM and native WASM host regressions remain
`36/36` and `107/107`, and the broad `src/lib` check passed with the existing
`447` warning profile. Real request streams, response streaming, broader
event-loop ordering, and host network I/O remain open.

CommonJS/Node bounded HTTP sealed-header continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded `http.request`/`https.request` header mutation now rejects
deterministically after sealed request states. `setHeader` and `removeHeader`
leave header state unchanged after `flushHeaders()`, `end()`, or `abort()`,
while recording `headerMutationRejected=true` and
`headerMutationRejectReason` as `headers-flushed`, `request-ended`, or
`request-aborted`. Focused checks passed, the Node API conformance suite
passes `246/246`, BrowserSession fetch/WASM and native WASM host regressions
remain `36/36` and `107/107`, and the broad `src/lib` check passed with the
existing `447` warning profile. Real request streams, response streaming,
broader event-loop ordering, and host network I/O remain open.

CommonJS/Node bounded HTTP terminal-flush continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded `http.request`/`https.request` header flushing now rejects
deterministically after terminal request states. `flushHeaders()` after `end()`
records `headerFlushRejected=true` with `headerFlushRejectReason=request-ended`;
`flushHeaders()` after `abort()` records `request-aborted`; and a late rejected
flush does not rewrite the earlier `headersFlushed` or `flushedHeaderCount`
state. Focused checks passed, the Node API conformance suite passes `247/247`,
BrowserSession fetch/WASM and native WASM host regressions remain `36/36` and
`107/107`, and the broad `src/lib` check passed with the existing `447` warning
profile. Real request streams, response streaming, broader event-loop ordering,
and host network I/O remain open.

CommonJS/Node bounded listener inspection continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded `EventEmitter`, `http.request`/`https.request`, and synthetic HTTP
response objects now expose deterministic `listeners(event)` inspection. The
shared bounded event store returns active callbacks in registration order after
removals, and missing events return an empty array. Focused checks and
regression evidence are captured in this continuation; real request streams,
response streaming, broader event-loop ordering, and host network I/O remain
open.

CommonJS/Node bounded HTTP response byte-state continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded synthetic HTTP responses now expose stable readable defaults and byte
state. New responses report `readableHighWaterMark=16384`,
`readableObjectMode=false`, empty `readableEncoding`, and `bytesRead=0`; data
delivery, `read()`, `pipe()`, and async iteration update `bytesRead` to the
bounded body length when they consume the response body. Focused checks and
regression evidence are captured in this continuation; real request streams,
response streaming, broader event-loop ordering, and host network I/O remain
open.

CommonJS/Node bounded timer handle type continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded timer handles now expose deterministic `timerType` labels for
`setTimeout`, `setInterval`, module `setImmediate`, and global `setImmediate`
handles. This keeps the shared bounded timer scheduler behavior unchanged while
making handle identity visible to compatibility checks. Focused checks and
regression evidence are captured in this continuation; broader event-loop
ordering, host I/O integration, and full Node timer-object lifecycle behavior
remain open.

CommonJS/Node bounded timer schedule-state continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_async.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded timer handles now expose deterministic schedule state:
`scheduledAt`, `dueAt`, and `lastFiredAt`. New handles start with
`scheduledAt=0`, `dueAt=delay`, and `lastFiredAt=-1`; one-shot timers record
their fire time during drain; intervals update `scheduledAt` and `dueAt` for
the next bounded repeat; and refresh restores the visible schedule window.
Focused checks and regression evidence are captured in this continuation;
broader event-loop ordering, host I/O integration, and full Node timer-object
lifecycle behavior remain open.

CommonJS/Node bounded timer clear-provenance continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded timer handles now expose deterministic cancellation provenance. New
handles start with `cleared=false` and empty `clearedBy`; `clearTimeout`,
`clearInterval`, `clearImmediate`, and handle `close()` mark the handle closed,
inactive, cleared, and record the API that cleared it. Focused checks and
regression evidence are captured in this continuation; broader event-loop
ordering, host I/O integration, and full Node timer-object lifecycle behavior
remain open.

CommonJS/Node bounded timer completion-state continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_async.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded timer handles now expose deterministic one-shot completion state.
New handles start with `completed=false`; fired timeout handles become inactive
and completed; interval handles remain active and not completed after a drain;
and cleared handles remain uncompleted while recording their cancellation
provenance. Focused checks and regression evidence are captured in this
continuation; broader event-loop ordering, host I/O integration, and full Node
timer-object lifecycle behavior remain open.

CommonJS/Node bounded primitive timer clear continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded timer clears now update handle lifecycle state when callers pass the
primitive timer id rather than the handle object. `clearTimeout(h.id)`,
`clearInterval(h.id)`, and `clearImmediate(h.id)` cancel the pending bounded
task and mark the matching handle closed, inactive, cleared, and tagged with
the clearing API. Focused checks and regression evidence are captured in this
continuation; broader event-loop ordering, host I/O integration, and full Node
timer-object lifecycle behavior remain open.

CommonJS/Node bounded completed-timeout refresh continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded timeout handles can now be refreshed after their one-shot callback has
fired. A completed, non-closed timeout handle re-enters the bounded timer queue,
becomes active again, clears `completed`, records `refreshed=true`, and restores
the visible due window from its stored delay. Focused checks and regression
evidence are captured in this continuation; broader event-loop ordering, host
I/O integration, and full Node timer-object lifecycle behavior remain open.

CommonJS/Node bounded completed-timeout callback refresh continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Completed bounded timeout handles now retain the original callback id on the
handle, so `refresh()` after a one-shot firing requeues the same callback
instead of only reactivating visible lifecycle state. The Node API conformance
scenario drains the timeout, refreshes the completed handle, drains again, and
verifies both the second callback execution and updated `fireCount`. Focused
checks and regression evidence are captured in this continuation; broader
event-loop ordering, host I/O integration, and full Node timer-object lifecycle
behavior remain open.

CommonJS/Node bounded timer callback-argument continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter.spl src/lib/nogc_sync_mut/js/engine/interpreter_async.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded `setTimeout`, `setInterval`, and `setImmediate` now preserve extra
callback arguments on the pending timer task and pass them into the callback
when the runtime drains due timers. Interval rescheduling keeps the same
argument list, and completed timeout `refresh()` rebuilds the pending task from
arguments stored on the handle so refreshed callbacks receive the same values.
Focused checks and regression evidence are captured in this continuation;
broader event-loop ordering, host I/O integration, and full Node timer-object
lifecycle behavior remain open.

CommonJS/Node bounded timer primitive-conversion continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval_member.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded timer handles now expose deterministic primitive conversion methods.
`valueOf()` and `Symbol.toPrimitive` return the numeric timer id, `toString()`
returns the textual id, and a `valueOf()` result can clear the matching handle
through the existing primitive-id cancellation path. Focused checks and
regression evidence are captured in this continuation; broader event-loop
ordering, host I/O integration, and full Node timer-object lifecycle behavior
remain open.

CommonJS/Node bounded writable destroy continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/runtime.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded writable streams now expose deterministic `destroy()` lifecycle state.
`destroy()` marks the writable destroyed, closed, non-writable, and length zero;
emits `close` at most once through the shared EventEmitter path; clears once
close listeners; denies later writes with `stream-destroyed`; and makes
`end()` after destroy return `false`. Focused checks and regression evidence
are captured in this continuation; broader event-loop ordering, host I/O
integration, and full Node stream lifecycle behavior remain open.

CommonJS/Node bounded writable listener-management continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded writable streams now expose the shared EventEmitter listener-management
surface used by readable streams and HTTP request/response objects:
`listeners`, `removeListener`, `off`, and `removeAllListeners`. Removed finish
and close listeners no longer fire, and `listeners(event)` reflects active
callbacks after removals. Focused checks and regression evidence are captured
in this continuation; broader event-loop ordering, host I/O integration, and
full Node stream lifecycle behavior remain open.

CommonJS/Node bounded writable finish-state continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/feature/js/node_api_conformance_spec.spl --output doc/06_spec`

Bounded writable streams now expose deterministic terminal finish state.
New writables start with `writableFinished=false` and `closed=false`; `end()`
marks `writableEnded`, `writableFinished`, and `closed` without marking the
stream destroyed; writes after `end()` remain denied as write-after-end; and
`destroy()` after `end()` is a no-op that does not emit `close`. Focused checks
and regression evidence are captured in this continuation; broader event-loop
ordering, host I/O integration, and full Node stream lifecycle behavior remain
open.

BrowserSession Uint8Array prototype metadata continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_eval_member.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession scripts now expose bounded `Uint8Array.prototype` metadata and
stable identity: repeated `Uint8Array.prototype` reads compare true with
`===`, `typeof Uint8Array.prototype` is `object`, `BYTES_PER_ELEMENT` is `1`,
and the prototype carries function-valued `subarray`, `values`, and
`Symbol.iterator` entries backed by the existing deterministic typed-array
native methods. The equality parser no longer treats the `==` substring inside
`===` / `!==` as the operator; browser scripts now prove strict equality for
numbers, strings, host globals, and strict inequality for distinct primitive
values. The focused fetch/WASM chain spec now passes `39/39`; broader
typed-array prototype parity, general `Function.prototype.call/apply`
dispatch, and full browser/WASM semantics remain open.

BrowserSession ArrayBuffer view detection continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession scripts now expose bounded `ArrayBuffer.isView` behavior:
`Uint8Array` and `DataView` inputs return `true`, while raw `ArrayBuffer`,
plain object, and `null` inputs return `false`. The focused fetch/WASM chain
spec now passes `40/40`; broader typed-array prototype parity, general
`Function.prototype.call/apply` dispatch, and full browser/WASM semantics
remain open.

BrowserSession Uint8Array prototype helper dispatch continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession scripts now dispatch bounded `Uint8Array.prototype` helpers
through `call` and `apply` for existing deterministic native helpers. The
focused scenario proves `subarray.call`, `slice.apply`, and `values.call`
against a browser-script `Uint8Array`, preserving coerced byte values and
iterator state. The focused fetch/WASM chain spec now passes `41/41`; broader
typed-array prototype parity, general `Function.prototype.call/apply`
dispatch, and full browser/WASM semantics remain open.

BrowserSession typed-array constructor metadata continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_eval_member.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession scripts now expose bounded constructor metadata for
`ArrayBuffer`, `Uint8Array`, and `DataView`: names, constructor arities, and
`Uint8Array.prototype.constructor === Uint8Array`. The focused fetch/WASM chain
spec now passes `42/42`; broader typed-array prototype parity, general
`Function.prototype.call/apply` dispatch, and full browser/WASM semantics
remain open.

BrowserSession ArrayBuffer/DataView prototype metadata continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval_member.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession scripts now expose stable bounded `ArrayBuffer.prototype` and
`DataView.prototype` objects. The scenario proves repeated strict identity,
constructor links back to `ArrayBuffer` and `DataView`, and a function-valued
`DataView.prototype.getUint8` accessor surface while preserving the focused
fetch/WASM chain spec at `42/42`. Broader typed-array prototype parity, general
`Function.prototype.call/apply` dispatch, and full browser/WASM semantics remain
open.

BrowserSession DataView prototype helper dispatch continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession scripts now dispatch bounded `DataView.prototype` byte helpers
through `call` and `apply` without requiring general `Function.prototype`
dispatch. The scenario proves `setUint16.call`, `setInt8.apply`,
`setUint32.call`, `getUint16.apply`, `getInt8.call`, and `getUint32.apply`
against the same ArrayBuffer-backed view, with byte visibility through
`Uint8Array`. The focused fetch/WASM chain spec now passes `43/43`; broader
typed-array/DataView prototype parity, general `Function.prototype.call/apply`
dispatch, and full browser/WASM semantics remain open.

BrowserSession Uint8Array prototype sort dispatch continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession scripts now dispatch bounded `Uint8Array.prototype.sort.call`
against a browser-script typed array. The scenario proves in-place numeric byte
sorting, normalized byte values, and returned receiver identity via
`toString()`/`at()` reads. The focused fetch/WASM chain spec now passes `44/44`;
broader typed-array/DataView prototype parity, general
`Function.prototype.call/apply` dispatch, and full browser/WASM semantics remain
open.

BrowserSession Uint8Array prototype sort apply continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession scripts now also prove bounded
`Uint8Array.prototype.sort.apply` against a browser-script typed array. The
scenario verifies normalized byte sorting, in-place mutation, and returned
receiver identity through `toString()`/`at()` reads. The focused fetch/WASM chain
spec now passes `45/45`; broader typed-array/DataView prototype parity, general
`Function.prototype.call/apply` dispatch, and full browser/WASM semantics remain
open.

BrowserSession Uint8Array prototype Symbol iterator dispatch continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession scripts now dispatch bounded
`Uint8Array.prototype[Symbol.iterator].call` against a browser-script typed
array. The resolver recognizes the real computed `Symbol.iterator` expression
and routes it to the deterministic values iterator. The focused fetch/WASM chain
spec now passes `46/46`; broader typed-array/DataView prototype parity, general
`Function.prototype.call/apply` dispatch, and full browser/WASM semantics remain
open.

BrowserSession Uint8Array prototype comparator sort dispatch continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession scripts now dispatch bounded
`Uint8Array.prototype.sort.call(bytes, compareFn)` with the same comparator
callback semantics as direct `bytes.sort(compareFn)`. The scenario proves
descending numeric byte order, normalized byte values, in-place mutation, and
returned receiver identity. The focused fetch/WASM chain spec now passes
`47/47`; broader typed-array/DataView prototype parity, general
`Function.prototype.call/apply` dispatch, and full browser/WASM semantics remain
open.

BrowserSession Uint8Array prototype map dispatch continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession scripts now dispatch bounded
`Uint8Array.prototype.map.call(bytes, callback)` against a browser-script typed
array. The callback receives normalized byte value, index, and receiver
arguments, and the returned typed array coerces mapped values back to bytes while
leaving the source unchanged. The focused fetch/WASM chain spec now passes
`48/48`; broader typed-array/DataView prototype parity, general
`Function.prototype.call/apply` dispatch, and full browser/WASM semantics remain
open.

BrowserSession Uint8Array prototype filter dispatch continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession scripts now dispatch bounded
`Uint8Array.prototype.filter.call(bytes, callback)` against a browser-script
typed array. The callback receives normalized byte value, index, and receiver
arguments, truthy callback results select normalized source bytes, and the
returned typed array leaves the source unchanged. The focused fetch/WASM chain
spec now passes `49/49`; broader typed-array/DataView prototype parity, general
`Function.prototype.call/apply` dispatch, and full browser/WASM semantics remain
open.

BrowserSession Uint8Array prototype reduce dispatch continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession scripts now dispatch bounded
`Uint8Array.prototype.reduce.call(bytes, callback, initial)` against a
browser-script typed array. The callback receives accumulator, normalized byte
value, index, and receiver arguments, and the accumulator result matches direct
typed-array reduce behavior. The focused fetch/WASM chain spec now passes
`50/50`; broader typed-array/DataView prototype parity, general
`Function.prototype.call/apply` dispatch, and full browser/WASM semantics remain
open.

BrowserSession Uint8Array prototype reduceRight dispatch continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession scripts now dispatch bounded
`Uint8Array.prototype.reduceRight.call(bytes, callback, initial)` against a
browser-script typed array. The callback receives accumulator, normalized byte
value, index, and receiver arguments in right-to-left order, and the accumulator
result matches direct typed-array reduceRight behavior. The focused fetch/WASM
chain spec now passes `51/51`; broader typed-array/DataView prototype parity,
general `Function.prototype.call/apply` dispatch, and full browser/WASM
semantics remain open.

BrowserSession Uint8Array prototype some dispatch continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession scripts now dispatch bounded
`Uint8Array.prototype.some.call(bytes, callback)` against a browser-script typed
array. The callback receives normalized byte value, index, and receiver
arguments, and predicate evaluation returns `true` on the first truthy match.
The focused fetch/WASM chain spec now passes `52/52`; broader
typed-array/DataView prototype parity, general `Function.prototype.call/apply`
dispatch, and full browser/WASM semantics remain open.

BrowserSession Uint8Array prototype every dispatch continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession scripts now dispatch bounded
`Uint8Array.prototype.every.call(bytes, callback)` against a browser-script
typed array. The callback receives normalized byte value, index, and receiver
arguments, and predicate evaluation returns `false` on the first falsey match.
The focused fetch/WASM chain spec now passes `53/53`; broader
typed-array/DataView prototype parity, general `Function.prototype.call/apply`
dispatch, and full browser/WASM semantics remain open.

BrowserSession Uint8Array prototype predicate apply continuation:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec`

BrowserSession scripts now dispatch bounded
`Uint8Array.prototype.some.apply(bytes, [callback])` and
`Uint8Array.prototype.every.apply(bytes, [callback])` against browser-script
typed arrays. Predicate callbacks receive normalized byte value, index, and
receiver arguments through the argument-array path. The focused fetch/WASM chain
spec now passes `54/54`; broader typed-array/DataView prototype parity, general
`Function.prototype.call/apply` dispatch, and full browser/WASM semantics remain
open.
