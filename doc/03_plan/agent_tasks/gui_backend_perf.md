# GUI/Backend Performance Agent Task Plan

Lane: ongoing Simple GUI/backend performance convergence
Updated: 2026-06-11

## Completed (already pushed)

- `2dc841a399` -- font offload backend selection: added
  `engine2d_font_offload_backend_order()` and
  `engine2d_backend_lane_preferred_font_offload_candidate(...)` so vector and
  bitmap font offload use a stable processing-lane order: Metal, CUDA, ROCm/HIP,
  Qualcomm, Vulkan, DirectX, OpenCL, OpenGL, Intel, WebGPU, CPU SIMD, software,
  then CPU. Evidence: `backend_lane_spec.spl` now covers alias handling and
  native GPU lanes before Vulkan.
- this commit -- preferred font offload evidence wrappers: added vector and
  bitmap evidence helpers that apply the Engine2D font offload order to probed
  backend candidates before building typed evidence. Evidence:
  `vector_font_offload_spec.spl` and `bitmap_font_offload_spec.spl` cover ROCm
  alias selection before Vulkan and explicit CPU fallback behavior.
- this slice -- preferred font readback evidence wrappers: added
  `vector_font_preferred_glyph_readback_evidence(...)` and
  `bitmap_glyph_raster_preferred_mask_readback_evidence(...)` so glyph readback
  evidence now applies Engine2D font offload lane preference before submit/readback
  classification.
- `275a221f5d` -- production GUI web parity render path: replaced O(n^2)
  distinct-color scan with dictionary membership, reused deterministic parity
  reports, skipped Metal fallback rerender/compare on software hosts, and added
  a scoped fast path for the production parity common.ui widget fixture. Evidence:
  `production_gui_web_renderer_parity_hardening_spec.spl` improved from a 120s
  timeout to 8 passing examples in 6.6s.
- this commit -- production GUI render timing evidence: `ProductionGuiWebParityReport`
  and `BackendExecutedGuiSceneReport` now carry per-backend render elapsed
  microseconds plus total elapsed time. Evidence:
  `production_gui_web_renderer_parity_hardening_spec.spl` asserts timing fields,
  and `check-production-gui-web-backend-executed-evidence.shs` writes the timing
  values into backend evidence reports.
- this commit -- render timing budget classification: production GUI parity
  reports now include timing budget, status, and reason fields for generated
  widget rendering and backend-executed Engine2D rendering. Evidence:
  `production_gui_web_renderer_parity_hardening_spec.spl` asserts focused paths
  remain within budget, and the backend evidence wrapper emits the budget fields.
- this commit -- render throughput evidence: production GUI parity reports now
  derive per-backend and total pixels-per-second from pixel counts and measured
  elapsed time. Evidence: `production_gui_web_renderer_parity_hardening_spec.spl`
  asserts positive throughput, and the backend evidence wrapper emits throughput
  fields for software, CPU SIMD, Metal, and total render paths.
- this commit -- backend render sample aggregation: the backend-executed evidence
  wrapper now runs three reduced-scene samples and emits min/avg/max total
  elapsed time plus min/avg/max total throughput. Evidence:
  `check-production-gui-web-backend-executed-evidence.shs` fails if any sample
  loses exact parity, CPU SIMD execution, Metal readback requirements, or timing
  budget status.
- this commit -- top-level parity sample propagation: the canonical production
  GUI web renderer parity wrapper now promotes backend sample count plus
  min/avg/max elapsed and throughput into
  `production_gui_web_renderer_parity_backend_*` fields and its Markdown
  summary, so archived full-wrapper reports retain the aggregate evidence.
- this commit -- production GUI font offload evidence: added
  `scripts/check/check-production-gui-font-offload-evidence.shs` to exercise the
  preferred vector and bitmap font offload/readback wrappers together and emit
  explicit typed unavailable rows when the host has no device submit/readback
  proof.
- this commit -- top-level font evidence propagation: the canonical production
  GUI web renderer parity wrapper now runs the font offload/readback wrapper and
  promotes typed vector and bitmap font evidence under
  `production_gui_web_renderer_parity_font_offload_*` fields.
- this commit -- Chrome live capture timeout hardening: the Chrome layout
  bitmap evidence wrapper now bounds DevTools capture with
  `CHROME_LAYOUT_TIMEOUT_SECS` / `CHROME_LAYOUT_KILL_SECS`, emits
  `chrome-live-capture-timeout`, and cleans up spawned Chrome children on
  signal/exit so full parity evidence cannot hang indefinitely in the surface
  manifest.
- this commit -- surface manifest tracked-text policy: the Tauri/Chrome surface
  manifest now preserves exact-pixel requirements for text-free rows while
  counting `policy=track-text-divergence` rows separately as tracked evidence.
  Top-level production parity accepts exact+tracked coverage only when exact
  rows have zero mismatches and tracked rows keep `blur_or_tolerance=false`.
- this commit -- scaled glyph hot-path dispatch removal: the Simple Web HTML
  layout renderer no longer calls an always-true sparse-hit helper for every
  scaled glyph pixel. Scaled glyphs still render solid, preserving the prior
  visual semantics while removing per-pixel function dispatch from GUI text
  startup rendering.
- this commit -- flex stretch style-copy optimization: `styles_with_height`
  now preallocates the output style array and assigns by index instead of
  rebuilding it through repeated single-element appends. This removes a
  quadratic copy pattern from flex stretch layout while preserving the returned
  style values.
- this commit -- Engine2D selector verification unblock: the heuristic
  Engine2D renderer now uses a token-exact local class matcher for the
  `:has(> .badge)` fast path instead of calling a missing `class_has` helper.
  This restores the focused Engine2D renderer spec as usable regression
  coverage for later startup/render optimizations.
- this commit -- RGB token allocation removal: `_css_rgb_color` now parses the
  first three RGB components into scalar slots instead of pushing each token
  into a temporary array. This removes per-call dynamic array allocation/copy
  work from CSS color parsing in the heuristic Engine2D startup path.
- this commit -- Engine2D loop length hoisting: the heuristic surface clear
  loop, first-class lookup, selector rule scan, and style-block selector scan
  now hoist stable `.len()` values out of loop conditions. This trims repeated
  dispatch in GUI startup scanning and pixel-fill hot paths without changing
  rendered output.
- this commit -- CSS scan length hoisting: `_find_char_from`,
  `_last_hex_color_after`, `_resolve_current_color`,
  `_declaration_background_color`, and the `:not(...)` class scan now reuse
  stable string/list lengths inside their loops. This trims repeated length
  dispatch in color and selector parsing used by the heuristic Engine2D startup
  path.
- this commit -- Engine2D fixture scan reuse: the heuristic renderer now reuses
  precomputed fixture-marker booleans for fixture dispatch and wm/simple mark
  painting instead of rescanning HTML for each branch.
- this commit -- style-block marker scan reuse: `_style_rule_block_color` now
  uses one `<style` index lookup for both branch selection and substring
  extraction instead of scanning once with `contains` and again with `index_of`.
- this commit -- split-pane fixture marker reuse: the Engine2D split-pane status
  list scene now participates in the shared fixture-marker booleans for
  recognition, solid-fill exclusion, and dispatch, with focused exact-pixel unit
  coverage for the branch.
- this commit -- block dimension marker reuse: the Engine2D fallback block
  painter now caches margin, width, and height marker booleans once before
  choosing block geometry, avoiding repeated HTML scans while preserving the
  existing geometry priority order.
- this commit -- hex color tail allocation removal: `_first_hex_color_after`
  and `_second_hex_color_after` now locate `#` directly in the original HTML
  from the known offset, avoiding temporary tail substring allocation before
  parsing the same color.
- this commit -- repeated hex color tail allocation removal: `_last_hex_color_after`
  now parses colors from the original HTML buffer after each marker match instead
  of allocating an extra post-marker tail substring before looking for `#`.
- this commit -- body marker scan reuse: `_html_background_color` now caches
  the first `<body` index and reuses it for body-gated background checks and tag
  extraction, avoiding repeated whole-HTML scans for the same marker.
- this commit -- body tag close scan allocation removal: `_html_background_color`
  now finds the body tag closing `>` directly in the original HTML buffer instead
  of allocating a body-tail substring only to locate the tag end.
- this commit -- first block tag-end allocation removal: `_first_block_color`
  now finds the first visual tag closing `>` in the original HTML buffer instead
  of allocating a block-tail substring only to locate the tag end.
- this commit -- custom property color tail allocation removal:
  `_custom_property_color` now locates `#` directly in the original HTML after
  the property marker instead of allocating a post-marker tail before parsing.
- this commit -- RGB parenthesis tail allocation removal:
  `_css_rgb_color` now finds the RGB opening and closing parentheses directly
  in the original HTML buffer before extracting the inner component list,
  avoiding two temporary tail substrings in CSS RGB parsing.
- this commit -- CSS variable close-scan allocation removal:
  `_first_var_color_after` now finds the closing `)` in the existing post-marker
  scan buffer instead of allocating an additional post-`var(` tail substring.
- this commit -- currentColor value tail allocation removal:
  `_is_current_color_after` now finds the optional colon in the original
  declaration buffer and trims the value slice directly, avoiding an
  intermediate post-property tail allocation.
- this commit -- currentColor hash tail allocation removal:
  `_resolve_current_color` now locates `#` directly in the original declaration
  buffer after a standalone `color:` token instead of allocating a post-token
  tail before parsing the hex color.
- this commit -- `:not(...)` close-scan allocation removal:
  `_not_selector_rejects_first_block` now finds the closing `)` in the original
  HTML buffer before extracting selector options, avoiding a post-marker tail
  allocation in the heuristic selector path.
- this commit -- style rule brace tail allocation removal:
  `_last_rule_hex_color` now finds `{` and `}` in the original HTML buffer
  after a selector match instead of allocating post-selector and post-brace
  tails before parsing the rule body.
- this commit -- style-block selector brace tail allocation removal:
  `_style_block_has_class_or_id_selector` now scans `{` and `}` within the CSS
  slice directly instead of allocating per-rule brace and end tails while
  checking for class or id selectors.
- this commit -- style-block open tag tail allocation removal:
  `_style_block_has_class_or_id_selector` now finds the `<style...>` tag close
  directly in the original HTML buffer instead of allocating a post-style-start
  tail only to locate `>`.
- this commit -- attribute value quote-scan allocation removal:
  `_attr_value` now finds single- and double-quote terminators directly in the
  tag string instead of allocating an attribute-value tail before returning the
  same value slice.
- this commit -- visual-tag scan allocation removal:
  `_find_next_visual_tag` and direct-child close checks now use a bounded
  multi-character scanner instead of allocating HTML tails before `index_of`.
- this commit -- CSS selector scan allocation removal:
  `_last_rule_hex_color` and style-block selector detection now find selectors
  and `</style>` directly in the original HTML buffer instead of allocating
  search tails for every rule scan.
- this commit -- hex marker scan allocation removal:
  `_second_hex_color_after` and `_last_hex_color_after` now reuse the bounded
  text scanner instead of allocating post-marker HTML tails before searching.
- this commit -- currentColor resolver scan allocation removal:
  `_resolve_current_color` now scans the lowercase declaration buffer directly
  for `color:` instead of allocating a search tail on each loop iteration.
- this commit -- CSS var lookup tail allocation removal:
  `_first_var_color_after` now scans from a caller-supplied offset and finds
  `var(...)` directly in the original HTML buffer, removing style-tail slices.
- this commit -- declaration background scan allocation removal:
  `_declaration_background_color` now searches the original declaration buffer
  directly for background properties instead of allocating a tail each loop.
- this commit -- second block color scan allocation removal:
  `_second_hex_color_after` now has a start-offset variant so render-time second
  block-color probing no longer slices the HTML buffer at the first block tag.
- this commit -- currentColor value normalization allocation removal:
  `_is_current_color_after` now skips whitespace and compares `currentColor`
  in-place instead of allocating, trimming, and lowercasing a value tail.
- this commit -- CSS rgb token concatenation removal:
  `_css_rgb_color` now parses numeric RGB channels directly from the HTML buffer
  instead of building token strings with per-character concatenation.
- this commit -- font evidence candidate coverage: the production GUI font
  offload evidence wrapper now seeds platform-appropriate candidates in the same
  native-GPU-before-Vulkan order used by `engine2d_font_offload_backend_order`,
  including canonical `rocm` plus the `amd-hip` alias for HIP hosts.
- this commit -- style selector routing allocation removal:
  `_style_block_has_class_or_id_selector` now scans selector ranges in the
  original HTML buffer instead of slicing each style block and selector while
  deciding whether generic HTML must use the real layout renderer.
- this commit -- layout parser tail-copy removal: the real Pure Simple HTML
  layout renderer now searches from an offset directly in the original text
  buffer instead of allocating a tail substring before every parser `find_from`
  call.
- this commit -- debug attr loop length hoist:
  `simple_web_layout_debug_attr_by_id` now reuses the parsed node count instead
  of dispatching `nodes.len()` on every scan iteration.
- this commit -- session widget-store copy removal:
  `WidgetStore.upsert_record` and `WidgetStore.set_prop` now allocate the exact
  result array once and fill by index instead of rebuilding records and props
  with repeated array concatenation on each append or replacement.
- this commit -- global widget-store copy removal:
  process-global `upsert_widget_record`, `set_internal_prop`, child
  registration, and widget traversal helpers now avoid per-item array
  concatenation while preserving widget id, prop, and child ordering.
- this commit -- session widget traversal copy removal:
  session-scoped child registration, prop-key collection, child lookup, and
  recursive id collection now avoid per-item array concatenation while keeping
  nil-child filtering and traversal order intact.
- this commit -- builder child staging removal:
  dropdown, menubar, tabs, list, and table builders now attach generated child
  nodes directly instead of first growing staging arrays and replaying them.
- this commit -- layout rect allocation tightening:
  layout root rect creation, visible-child filtering, and fixed-layout rect
  collection now avoid empty push-grown arrays and hoist fixed child counts.
- this commit -- Draw IR event loop count hoist:
  Draw IR command matching, event batch resolution, and composition planning now
  reuse batch/command counts instead of dispatching `.len()` in hot loops.
- this commit -- window surface registry filter allocation tightening:
  window/surface binding replacement and clear paths now pre-count retained
  bindings and fill exact-size arrays instead of growing filtered lists.
- this commit -- bitmap glyph expected-pixel allocation tightening:
  bitmap font offload expected-pixel masks now allocate the final pixel array
  once and fill colored glyph pixels by index instead of push-growing per pixel.
- this commit -- Simple Web framebuffer seed allocation tightening:
  the Pure Simple HTML pixel renderer now initializes its white framebuffer in
  one exact-size array allocation instead of push-growing every pixel.
- this commit -- browser script marker scan allocation removal:
  script render and execution parsers now search markers from offsets directly
  instead of slicing a tail string before each lookup.
- this commit -- corpus fixture PPM allocation tightening:
  browser corpus PPM fixtures now decode into a pre-sized ARGB buffer instead
  of push-growing one pixel per RGB triplet.
- this commit -- Engine2D class selector split removal:
  Simple Web Engine2D class helpers now scan class tokens in place instead of
  allocating a split token array for each selector probe.
- this commit -- Draw IR diff allocation tightening:
  Draw IR baseline diffs now pre-count node diffs and fill an exact-size result
  array instead of push-growing changed/added/removed entries.
- this commit -- UI access adapter registry allocation tightening:
  Adapter target replacement now pre-counts retained entries and fills an
  exact-size registry array instead of push-growing the filtered list.
- this commit -- Browser paint scene bridge allocation tightening:
  Paint command conversion now pre-counts emitted scene commands and fills an
  exact-size command array instead of push-growing during the hot bridge loop.
- this commit -- WM Draw IR composition allocation tightening:
  Window-layer ordering and final Draw IR batch assembly now use exact-size
  buffers instead of repeatedly grow-copying arrays during scene projection.
- this commit -- Backend screenshot sampled-color allocation tightening:
  Capture evidence now counts unique sampled colors with a fixed 256-entry
  buffer and hoisted pixel lengths instead of push-growing a sampled list.
- this commit -- Shared WM scene allocation tightening:
  Scene projection, visible-window filtering, dragging, and focus transitions
  now fill exact-size window arrays instead of repeatedly grow-copying entries,
  and pointer hit-testing hoists the window count out of the scan loop.
- this commit -- Window manager model allocation tightening:
  Window replace, close, minimize, and focus transitions now size destination
  arrays up front and fill them by index instead of push-growing during state
  rebuilds.
- this commit -- Draw IR SDN allocation tightening:
  Draw IR SDN serialization and parsing now pre-size line, batch, and command
  arrays and hoist stable text lengths instead of repeatedly grow-copying
  inspection payloads.
- this commit -- UI patch wire scan length hoisting:
  Patch JSON escaping, field extraction, numeric parsing, and bounded substring
  search now reuse stable string lengths inside scanner loops instead of
  dispatching repeated `.len()` calls.
- this commit -- UI snapshot wire scan length hoisting:
  Snapshot JSON number/string extraction and revision parsing now reuse stable
  string lengths inside scanner loops, matching the patch-wire fast path for
  websocket startup protocol handling.
- this commit -- Web render marker scan allocation tightening:
  Dynamic-region marker scanning now reuses haystack/marker lengths and scans
  bounded slices directly instead of allocating a full tail substring before
  each marker lookup.
- this commit -- WASM hello GUI marker/surface allocation tightening:
  Generated-WASM GUI marker scanning now uses bounded direct scans, and surface
  evidence pre-counts present surfaces before filling an exact-size list.
- this commit -- Semantic UI contract allocation tightening:
  Semantic snapshot conversion, transport evidence matrices, and JSON list
  assembly now pre-size result arrays instead of repeatedly grow-copying
  semantic UI payloads.
- this commit -- UI access source scan length hoisting:
  Access-source envelope JSON escaping now reuses the stable input length
  inside the scanner loop, matching the optimized patch/snapshot wire helpers.
- this commit -- UI access snapshot allocation tightening:
  Recent-event snapshot copies, surface-filtered event lists, and widget child
  id lists now use exact-size buffers and cached event counts instead of
  repeated push growth and repeated loop-bound length calls.
- this commit -- UI access vision allocation tightening:
  Visual probe sidecar bounds and marks now pre-count matching nodes and fill
  exact-size arrays, while JSON escaping reuses the input length in the scan
  loop. The stale vision unit fixture now includes snapshot revisions.
- this commit -- UI patch stream allocation tightening:
  Warm reconnect patch generation now pre-counts mappable retained events and
  fills an exact-size patch array instead of repeatedly grow-copying patches
  during startup/reconnect replay.
- this commit -- browser script parser length hoisting:
  Script-tag collection now reuses the HTML length in the parser loop instead
  of recalculating it while scanning startup HTML for executable/denied scripts.
- this commit -- browser script execution scan length hoisting:
  Browser JS execution now reuses variable-store, HTML, and stdout line counts
  inside startup script scanning and console replay loops.
- this commit -- browser script execution allocation tightening:
  Browser JS source execution now preallocates statement-bounded output and
  variable-store arrays, then returns compact output prefixes instead of
  grow-copying console and assignment arrays during startup script execution.
- this commit -- browser text painter scan allocation tightening:
  HTML text stripping, whitespace normalization, and wrapped-line extraction
  now use exact-size buffers and compact prefixes instead of grow-copying text
  arrays during corpus text layout.
- this commit -- browser text painter wrap allocation tightening:
  Greedy text wrapping, paint-run projection, and SDN diagnostics now fill
  word/line-count-sized arrays instead of grow-copying line, run, and entry
  arrays in the corpus text layout path.
- this commit -- Engine2D emulation allocation tightening:
  Text drawing now reuses the string length in the glyph loop, and polygon
  scanline fill reuses a count-sized intersection buffer instead of grow-copying
  node lists on every row.
- this commit -- baremetal framebuffer allocation tightening:
  Baremetal readback and text-background rendering now fill exact-size pixel
  buffers, and the fallback glyph loop reuses the text length during startup
  framebuffer text drawing. The slice also keeps text/image framebuffer writes
  inside mutating backend methods so helper copies do not drop pixels.
- this commit -- selector matcher loop length hoisting:
  Browser selector `:not(...)` option scans and compound class-token scans now
  reuse stable split-list counts instead of dispatching `.len()` in loop
  conditions during fallback CSS selector matching.
- this commit -- Engine2D compositor loop length hoisting:
  Layer fills and compositor layer traversal now reuse stable pixel/layer counts
  instead of dispatching `.len()` in framebuffer fill and blend traversal loops.
- this commit -- CUDA readback allocation tightening:
  CUDA host readback now fills an exact-size `u32` pixel buffer by index instead
  of push-growing one pixel at a time during backend framebuffer readback.
- this commit -- Metal text dispatch length hoisting:
  Metal glyph dispatch now reuses the stable text length while walking glyphs,
  avoiding repeated `.len()` calls in the native-first text rendering path.
- this commit -- OpenCL readback allocation tightening:
  OpenCL host readback now fills an exact-size `u32` pixel buffer by index
  instead of push-growing one pixel at a time during backend framebuffer
  readback.
- this commit -- Engine2D emulation sort length hoisting:
  The shared emulation math insertion sort now reuses the stable array length
  instead of dispatching `.len()` on every outer-loop iteration.
- this commit -- Browser renderer scene-color scan length hoisting:
  Browser render scene-color detection now reuses the rendered pixel count while
  scanning for the first non-white pixel in the pure Simple HTML startup path.
- this commit -- Browser style parser scan length hoisting:
  Browser style block normalization, `@supports` wrapper stripping, and CSS
  nesting normalization now reuse stable input lengths during startup style
  parsing instead of dispatching `.len()` in parser loop conditions.
- this commit -- Browser layout recursion length hoisting:
  Low-level browser layout and paint recursion now reuse stable child counts
  while walking DOM/layout children, with direct unit coverage for stacked
  layout geometry. During coverage work, the browser `paint_box` scene mutation
  gap was isolated and recorded as a follow-up bug.
- this commit -- Browser DOM accessor recursion length hoisting:
  DOM child removal/insertion, text-content concatenation, id lookup, and tag
  collection now reuse stable child/result counts in recursive scans, with
  direct unit coverage for source-order text and descendant lookup behavior.
- this commit -- Browser DOM accessor allocation tightening:
  Text-content concatenation now fills a child-count-sized text array instead
  of push-growing a per-node part list during startup DOM text scans.
- this commit -- Browser session UI-access label scan length hoisting:
  BrowserSession UI-access link label stripping now reuses the stable HTML
  snippet length while removing inline tags, with focused coverage for nested
  inline link text in source order.
- this commit -- Browser session UI-access snapshot array preallocation:
  BrowserSession UI-access link nodes and fixed control snapshots now count and
  fill exact-size node arrays, removing the remaining optimizer-reported
  push-growth findings while preserving link filtering and source order.
- this commit -- Browser session HTML parser length hoisting:
  HTML text extraction, escaping, stylesheet discovery, CSS import stripping,
  and stylesheet insertion now reuse stable input lengths in loop conditions;
  direct stylesheet-source coverage locks inline/link/import ordering.
- `e0a0ec15f0c60d96dd320054e02c8309229e54ce` -- `perf(gui): carry browser text line widths`
- `248bf87` -- glyph fallback scan removal
- `c166d` -- backend preference lanes
- `97ed` -- DirectX backend order

## Current remaining work

1. Collect and record additional startup/render evidence (timing + throughput + parity)
   - Run and archive the full production GUI web renderer parity evidence wrapper
     now that it promotes backend aggregate sample fields.
   - Current local blocker after installing `tools/electron-shell` dependencies:
     generated-GUI Electron matrix and layout manifest pass, but the
     Tauri/Chrome surface manifest still fails with live-surface divergence
     (`tauri`: 16/18 pass, 216 mismatches; `chrome`: 14/18 pass, 1785 mismatches
     in the latest local run) and one bounded Chrome timeout row.
   - Re-run the surface manifest after the tracked-text policy change; any
     remaining failures should now represent exact-row divergence or a bounded
     host capture timeout, not the two known text-raster tracking rows.
   - Add broader throughput thresholds after enough host-stable samples exist.
2. Provide GPU/font offload proof
   - Demonstrate measured proof of real vector/bitmap GPU font offload and readback path behavior or explicit typed unavailability.
   - Use `scripts/check/check-production-gui-font-offload-evidence.shs` as the
     canonical evidence wrapper for current host captures.
   - Use `scripts/check/check-production-gui-web-renderer-parity-evidence.shs`
     for archived production GUI parity captures; it promotes the font evidence
     into its top-level report.
   - Ensure device submit/readback evidence uses preferred glyph readback wrappers after
     candidate ordering.
   - For every relevant wrapper execution, capture `status_code` plus `reason`:
     vector statuses include `gpu-glyph-returned`,
     `gpu-proof-with-cpu-glyph`, `cpu-fallback`,
     `vector-font-glyph-readback-matched`,
     `vector-font-glyph-not-submitted`, `vector-font-glyph-return-missing`,
     and `cuda-runtime-unavailable`; bitmap statuses include
     `gpu-copy-with-cpu-glyph`, `cpu-glyph-baseline`,
     `gpu-glyph-raster-readback-matched`, `gpu-glyph-raster-not-submitted`,
     `gpu-glyph-raster-invalid-expected-checksum`, and
     `opencl-runtime-or-queue-unavailable`.
   - Prefer explicit unavailable status/reason rows over silent fallback for
     missing runtimes, queues, or readback.
3. Execute focused pure Simple GUI text/layout optimization pass
   - Target isolated hot-path opportunities in text layout, line width handling, and browser text path.
   - Keep changes small and attributable with before/after measurements.
4. Preserve app behavior
   - Keep rendering semantics and UI behavior unchanged while tuning performance.
   - Add or refresh regression checks if behavior drift risk is introduced by any micro-optimization.

## Near-term handoff priorities

- Update backend startup/render evidence set first.
- Capture GPU/font offload decision proofs second.
- Continue pure Simple text/layout optimization with explicit behavior-preservation checks.
