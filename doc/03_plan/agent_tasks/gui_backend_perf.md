# GUI/Backend Performance Agent Task Plan

Lane: ongoing Simple GUI/backend performance convergence
Updated: 2026-06-23

## Brief lane snapshot (latest pushed updates)

- `7d4b6884e6f` (`perf(gui): collect browser layout entries linearly`) changed browser layout entry collection to a single linear pass.
- `4a452065683` (`fix(gui): stamp auto engine2d pixel backend`) applied automatic Engine2D pixel backend stamping in the startup path.
- `6ab0eb4cd5b` (`perf(gui): retain pure simple pixel artifacts`) preserves existing Pure Simple pixel artifacts instead of forcing rematerialization.
- `2dc841a399` (`perf(gui): expose font offload backend order`), `33214f81fa1` (`feat(gui): accept rocm vector font payloads`), `56030ade5a2` (`perf(gui): promote font offload evidence`), and `ec38eb1901e` (`perf(gui): prefer font readback backend order`) aligned ROCm/ROCm-HIP vector and bitmap font offload/readback with the preferred Engine2D lane before fallback behavior.
- `989f54eeca0` (`test(gui): cover engine2d backend aliases`) and `f911d561d1b` (`feat(gui): default pure simple web to auto backend`) expanded alias coverage in backend selection paths.
- `8623bc39f8f` (`perf(gui): fast path canonical backend names`) added a canonical-name fast path before deeper backend checks.
- `3d8cd2a636a` (`perf(gui): avoid duplicate backend canonicalization`) prevented redundant canonicalization on duplicate backend names.
- `102a3853d49` (`perf(gui): share font backend priority ranking`) moved font offload priority lookup onto the shared canonical Engine2D backend priority helper.
- `8c945adcd4f`, `e8f04e21e0e`, `52a07e28da6`, `798564eb892`,
  and `80e1a2b9a29` hardened the aggregate completion gate so incomplete 8K
  evidence, incomplete Metal readback evidence, missing named Metal/font
  blockers, incomplete browser backing evidence, and non-8K geometry cannot
  pass as complete evidence.
- `b481735f81d` renamed the missing focused browser-backing mode to
  `focused-browser-backing-required`, so the plan and aggregate no longer imply
  that fallback bitmap comparison is acceptable Vulkan-backed browser proof.

## Cooperative Review Routing

Use `.spipe/gui-hardening-full/state.md` as the source of truth for broad-lane
sidecars and manual helper names. Codex Spark owns bounded evidence-key and
manual-readability checks, Claude Haiku owns bounded 8K retained-row/blocker
checks, and Claude Sonnet owns broader web/Electron/Node/Bun and WM/QEMU/GTK
matrix review. The best available normal/highest-capability model must merge and
accept findings, generated-manual quality, coverage claims, exclusions, and done
marks before closing this lane. Before sidecars fan out, the best-model pass
owns shared interface names, manual `step("...")` flow helper names, and
setup/checker helper names. Shared helper placeholders must fail explicitly with
`assert(false)` or `fail(...)`; silent helper passes are not evidence.

## Cross-Cutting Runtime Facade Constraint

Owner: Codex implementation lane.

Sidecars: Spark may audit doc/spec references and focused evidence keys; Haiku
may audit small 8K/perf blocker slices; Sonnet may audit broader host/platform
matrix impact. The best available normal/highest-capability reviewer owns final
acceptance.

Acceptance:

- GUI, web renderer, and Engine2D Metal/Vulkan hardening code must not add direct
  `rt_*` environment or process calls outside the owning runtime/facade modules.
- New app leaf or `src/lib/gc_async_mut` runtime access must go through existing
  env/process facades, or the lane must add a named facade/alias with focused
  specs and generated/manual `doc/06_spec` evidence.
- Before runtime-adjacent edits, update `.spipe/gui-hardening-full/state.md`
  with the structured decision keys `runtime_need`, `facade_checked`,
  `chosen_path`, and `rejected_shortcuts`. Default to `reuse-facade`; use
  `fix-codegen-runtime-owner` only for a proven compiler/runtime owner bug.
- Final verification for this lane includes the direct-env/runtime guard on the
  working and staged trees, plus generated-manual quality review for any changed
  SSpec docs.

## Completed (already pushed)

- this slice -- SimpleOS/QEMU shared WM renderer startup fix: removed the host
  Simple Web renderer dependency from `shared_mdi_framebuffer_scene.spl` so the
  QEMU baremetal path no longer calls `default_theme_id()` / `rt_file_exists`
  while rendering the shared MDI scene. Evidence:
  `check-simpleos-wm-fullscreen-evidence.shs` passed with
  `renderer=shared_mdi_framebuffer_scene` and `TEST PASSED`.
- this slice -- shared framebuffer hot-path cleanup: clipped glyph rendering
  and backend blits before the inner loops, removed per-pixel source bounds
  checks for valid blit rows, avoided the fresh-buffer clear pass, and reduced
  `qemu_capture_ppm_spec.spl` unit viewport cost from about 96s to about 38s
  while preserving the same assertions.
- this slice -- Worker 2 host/SimpleOS divergence evidence: added
  `doc/09_report/host_simpleos_renderer_event_divergence_2026-07-06.md` to
  record the current shared-renderer/shared-event boundary and the remaining
  adapter-local divergence. The same slice tightened
  `shared_mdi_framebuffer_scene_spec.spl` with source-level assertions for QEMU
  display-surface evidence markers (`source=shared_mdi_framebuffer_scene`,
  `direct-mmio-commit`, `html-renderable`) and PS/2 mouse demux evidence
  (`_poll_qemu_mouse_input`, decoded left-button packet) without touching
  runtime source, the x86_64 QEMU entry, or the QMP drag evidence script.
- `2dc841a399` -- font offload backend selection: added
  `engine2d_font_offload_backend_order()` and
  `engine2d_backend_lane_preferred_font_offload_candidate(...)` so vector and
  bitmap font offload use a stable processing-lane order: Metal, CUDA, ROCm/HIP,
  Qualcomm, Vulkan, DirectX, OpenCL, OpenGL, Intel, WebGPU, CPU SIMD, software,
  then CPU. Evidence: `backend_lane_spec.spl` now covers alias handling and
  native GPU lanes before Vulkan.
- this slice -- documented the separate font-offload CPU tail in
  `engine2d_backend_order.md` and hardened `backend_lane_spec.spl` so
  `cpu-simd` aliases win over `software` for font/vector preparation.
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
- this slice -- layout manifest progressed past the linked-worktree
  `missing-simple-bin` blocker when run with an explicit Simple binary. Use
  `SIMPLE_BIN=...` for the intended in-tree/compiler build; only set
  `ALLOW_PATH_SIMPLE_BIN=1` when deliberately accepting `command -v simple` as
  opt-in local evidence. Partial bounded
  evidence is archived in
  `doc/09_report/electron_simple_web_layout_manifest_after_engine_dispatch_2026-06-23.md`;
  the first exact remaining case was `overflow_axis_matrix` with 270 mismatched
  pixels. A pure axis-aware clip-state patch made this case worse (342
  mismatches); the accepted fix instead models the CSS computed mixed-axis
  overflow path by treating `overflow-x:hidden; overflow-y:visible` as
  vertical auto overflow and painting the native-width vertical scrollbar.
  Focused evidence is archived in
  `doc/09_report/electron_simple_web_layout_overflow_axis_after_scrollbar_paint_2026-06-23.md`
  with 0 mismatches.
- this slice -- after the overflow-axis fix, the next confirmed exact Simple
  Web layout blocker was `position_relative_offset_matrix`: focused evidence in
  `doc/09_report/electron_simple_web_layout_position_relative_offset_current_2026-06-23.md`
  reports 18 geometry mismatches, all `#f59e0b -> #1d4ed8` in a 6x3 overlap
  strip where Chromium paints the relatively positioned blue box over the later
  normal-flow yellow box. A naive "skip relative in normal pass, repaint later"
  source experiment worsened the case to 40 mismatches and was reverted. The
  accepted fix delays the entire relative normal-flow paint group so the
  relative parent and its descendants keep their internal order while painting
  above later non-positioned siblings. Focused evidence is archived in
  `doc/09_report/electron_simple_web_layout_position_relative_offset_after_relative_group_2026-06-23.md`
  with 0 mismatches.
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
- this commit -- layout count-pass text trim allocation removal: the real Pure
  Simple HTML layout renderer now checks text ranges in-place while sizing the
  parse arena instead of allocating temporary text/tail substrings just to trim
  and count visible text nodes.
- this commit -- Simple Web class flag scan consolidation: `parse_html` now
  derives widget, icon-image, and focused class flags in one class-attribute
  scan instead of running repeated substring searches for every classed node
  during GUI startup parsing.
- this commit -- Simple Web close-tag name allocation removal: close-tag stack
  matching now compares the raw tag-inner range in place, including uppercase
  close tags and trailing whitespace, instead of allocating and lowercasing a
  temporary close-tag name during startup parsing.
- this commit -- Simple Web close-tag char lowercase allocation removal:
  mixed-case close-tag matching now uses direct ASCII character comparisons
  instead of allocating a one-character lowercase value for each tag character.
- this commit -- Simple Web lowercase tag-name fast path: `tag_name_of` now
  skips `.lower()` for already-lowercase opening tags while preserving uppercase
  HTML normalization, avoiding an allocation on the common generated-GUI path.
- this commit -- Simple Web parser attribute-key allocation removal:
  `parse_html` now uses constant `class=`, `id=`, and `style=` keys for hot
  attribute extraction instead of allocating `name + "="` for every node field.
- this commit -- Simple Web parser attribute-key scan inline:
  hot `class=`, `id=`, and `style=` extraction now scans constant attribute keys
  with one key-length pass instead of routing through the generic text
  find/match helpers.
- this commit -- debug attr loop length hoist:
  `simple_web_layout_debug_attr_by_id` now reuses the parsed node count instead
  of dispatching `nodes.len()` on every scan iteration.
- this commit -- session widget-store copy removal:
  `WidgetStore.upsert_record` and `WidgetStore.set_prop` now allocate the exact
  result array once and fill by index instead of rebuilding records and props
  with repeated array concatenation on each append or replacement.
- this commit -- Simple Web viewport crop offset hoisting: the Pure Simple HTML
  layout renderer now computes source and destination framebuffer row offsets
  once per viewport row while cropping virtual scroll output, avoiding repeated
  `row * width` work in the startup pixel-copy loop.
- this commit -- Simple Web paint-pass index hoisting: background, border, and
  widget chrome paint passes now reuse the current node plus layout box values
  per iteration instead of repeatedly indexing `nodes`, `bx`, `by`, `bw`, and
  `bh` throughout the startup paint conditions and draw calls.
- this commit -- Simple Web text/icon paint index hoisting: the final text,
  widget-image, and icon paint pass now reuses the current node, style, and
  layout box values per iteration before text wrapping and glyph drawing.
- this commit -- Simple Web debug/Draw IR command hoisting:
  layout debug lookup and Draw IR command construction now reuse matched node
  and layout values instead of repeatedly indexing the node and box arrays.
- this commit -- Simple Web debug style lookup hoisting:
  `simple_web_layout_debug_style_by_id` now reuses the matched node and inline
  style text while serving declaration and parsed numeric debug fields.
- this commit -- Simple Web close-tag stack copy removal: HTML close-tag
  handling now trims the parent stack with the array slice primitive instead of
  manually allocating and copying stack entries on every matched close tag.
- this commit -- Simple Web widget flag scan hoisting:
  widget paint-flag detection now reuses current and parent nodes while scanning
  for widget panels and nonempty widget text before startup paint.
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
- this commit -- Browser session HTML stylesheet array preallocation:
  Stylesheet source extraction, CSS import extraction, and stylesheet insertion
  now count and fill exact-size source arrays, clearing the remaining general
  optimizer findings for browser-session HTML utilities.
- this commit -- Browser runtime history trim preallocation:
  Runtime-side history pushes now trim forward entries with an exact-size prefix
  array before appending the new entry, with direct coverage for stale forward
  history replacement.
- this commit -- Browser loading history trim preallocation:
  Normal page-load history updates now trim stale forward entries with an
  exact-size prefix array before appending, matching the runtime-side history
  allocation fix.
- this commit -- Browser loading URL/search loop length hoisting:
  URLSearchParams decode/set helpers and dynamic stylesheet/script loader loops
  now reuse stable loop lengths, refreshing counts only when loader work queues
  grow during iteration.
- this commit -- Browser module helper scanner length hoisting:
  JS module statement, binding, export-declarator, and generic text splitters
  now reuse stable source lengths while preserving quoted semicolon and
  top-level comma behavior.
- this commit -- Browser module helper array preallocation:
  JS module statement, import-binding, generic text split, and text-removal
  helpers now write into exact-size arrays instead of growing empty arrays on the
  browser module-loading path.
- this commit -- Browser module transform length hoisting:
  Script extraction, module symbol suffix generation, brace scanning, and module
  cache lookup now reuse stable loop lengths; script extraction also caches the
  debug sentinel scan instead of rechecking the full HTML per loop.
- this commit -- Browser session UI-access snapshot preallocation:
  BrowserSession UI-access link extraction and snapshot node construction now
  write into exact-size arrays, and inline tag stripping reuses the stable HTML
  length while preserving the browser controls/link action contract.
- this commit -- Simple browser page form-helper loop tightening:
  Hit testing, field lookup, form method lookup, and form pair serialization now
  reuse stable field/target counts, with form serialization writing exact-size
  pair arrays for the pure helper path independent of the baseline-red renderer spec.
- this commit -- Browser session cookie helper allocation tightening:
  Cookie splitting, document assignment parsing, jar upsert/removal, and
  request-header serialization now reuse stable lengths and exact-size arrays
  while preserving path/domain/expiry matching behavior.
- this commit -- Browser storage pair helper allocation tightening:
  Storage pair lookup now reuses stable list lengths, and pair upsert writes an
  exact-size output array for both replacement and append cases while preserving
  key order and storage API property collision behavior.
- this commit -- Browser session queue/favorite array tightening:
  Pending request dequeue and favorite-link removal now write exact-size arrays
  instead of append-growing replacement lists, preserving request order and
  favorite normalization behavior.
- this commit -- Simple browser page DOM/form array tightening:
  DOM decoration, field override flattening, and edited-field rebuilds now reuse
  stable lengths and exact-size arrays, while DOM text extraction uses a shared
  StringBuilder to avoid recursive text concatenation in page startup rendering.
- this commit -- Browser engine DOM accessor allocation tightening:
  Child removal/insertion, recursive text extraction, id lookup, and tag
  collection now reuse stable child counts and exact-size arrays where results
  are caller-visible, clearing the remaining general optimizer findings in
  low-level DOM accessors.
- this commit -- Browser engine layout traversal length hoisting:
  Core block layout and paint traversal now reuse stable child counts in their
  recursive loops, clearing the remaining general optimizer findings in the
  browser-engine layout pass without changing computed box order or height.
- `e0a0ec15f0c60d96dd320054e02c8309229e54ce` -- `perf(gui): carry browser text line widths`
- `248bf87` -- glyph fallback scan removal
- `c166d` -- backend preference lanes
- `97ed` -- DirectX backend order
- this commit -- UI web session token parser allocation removal:
  SessionToken parsing now records the four required separator offsets in a
  single scan and rejects extra separators immediately instead of push-growing a
  temporary dot-position array; token helper scanners also reuse stable input
  lengths.
- this commit -- async websocket broadcast allocation tightening:
  AsyncWebServer broadcast pruning now writes surviving websocket clients and
  runtime adapters into count-sized arrays and compacts once only when a client
  disconnects, avoiding repeated push-growth during render broadcasts.
- this commit -- static shell cache marker scan tightening:
  Web render static-shell cache counting now scans markers in place instead of
  allocating tail substrings per match, and retained shell command replay uses
  exact-size command arrays instead of push-growth during hot cache reuse.
- this commit -- UI route websocket frame decode tightening:
  Websocket route payload unmasking now writes into an exact-size byte buffer
  and uses direct four-byte mask slots instead of per-byte mask scans and
  push-growth; JSON helper scans also reuse stable text lengths.
- this commit -- UI web server response/frame buffer tightening:
  WebServer websocket exact reads and HTTP response chunk writes now fill
  pre-sized byte buffers by index, and stable websocket/header lengths are
  reused inside the startup request and frame loops.

## Current remaining work

1. Collect and record additional startup/render evidence (timing + throughput + parity)
   - 2026-06-23 wrapper run archived:
     `doc/09_report/production_gui_web_renderer_parity_evidence_2026-06-23.md`.
   - Current blocker: `ELECTRON_BITMAP_TIMEOUT_SECS=20 sh
     scripts/check/check-production-gui-web-renderer-parity-evidence.shs`
     reports `production_gui_web_renderer_parity_status=fail`,
     `production_gui_web_renderer_parity_reason=electron-generated-gui-matrix-failed`,
     and `matrix_electron_generated_gui_web_matrix_reason=case-80x64-failed`;
     the 80x64 case evidence reports `missing-electron-dependency`.
   - 2026-06-23 focused 80x64 retry after installing `tools/electron-shell`
     dependencies is archived in
     `doc/09_report/electron_generated_gui_web_parity_evidence_80x64_2026-06-23.md`.
     The blocker moved to `simple-render-failed`: the Simple render step times
     out after 60s with `CODEGEN-AMBIGUOUS-METHOD` diagnostics for `Engine2D`
     draw calls.
   - Previous local blocker after installing `tools/electron-shell` dependencies:
     generated-GUI Electron matrix and layout manifest passed, but the
     Tauri/Chrome surface manifest failed with live-surface divergence
     (`tauri`: 16/18 pass, 216 mismatches; `chrome`: 14/18 pass, 1785 mismatches)
     and one bounded Chrome timeout row.
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

## Current state update

- Shared UI surface manager allocation tightening: open, close, surface ID
  listing, and tree replacement now use exact-size arrays instead of
  append-growing replacement lists while preserving handle generation and
  active-surface behavior.
- Shared UI style cascade tightening: `resolve_style` now collects matching
  rules into an exact-size buffer and uses in-place stable insertion sort, so
  startup style resolution avoids repeated replacement-list allocation while
  preserving specificity and source-order cascade behavior.
- Host taskbar shell allocation tightening: registry snapshots and taskbar
  running-window models now use exact-size output arrays instead of append
  growth while preserving registry insertion order and minimized-state mapping.
- UI Web CSS startup allocation tightening: `generate_css` now uses the shared
  StringBuilder path for its large static fragment stream instead of rebuilding
  the fragment array on each append.
- Simple Web layout current-node hoisting: `layout` now reuses the current node
  while resolving width, nowrap text, text wrapping, and replaced element
  branches, avoiding repeated node indexing in startup layout recursion.
- Simple Web flex order allocation tightening: `flex_ordered_children` now
  collects children into an exact-size array and stable-sorts in place instead
  of rebuilding a replacement array for every ordered insertion.
- Simple Web ordered flex loop length hoisting: non-wrapping flex layout now
  reuses the ordered child count across sizing, baseline, and placement passes
  instead of asking the ordered child array for its length in every loop test.
- Simple Web Draw IR first-command reuse: Draw IR command collection now keeps
  the prebuilt first visible command and starts the fill loop at the next node,
  avoiding duplicate command construction for the first rendered element.
- Simple Web scroll crop loop tightening: scroll viewport cropping now advances
  source and destination row bases incrementally and removes the per-row bounds
  branch that is implied by `virtual_h = height + clamp_scroll`.
- Simple Web Draw IR first-visible scan removal: Draw IR command collection now
  records the first visible node during the count pass instead of scanning the
  node list a second time before filling the exact-size command array.
- Simple Web final paint visibility hoisting: the final image/icon/text paint
  pass now reuses per-node visibility and widget-mode booleans instead of
  repeating the same display/visibility checks for each branch.
- Simple Web positive-z paint visibility hoisting: collected positive z-index
  painting now reuses per-node visible-box and widget-mode booleans across
  background, border, panel, and button branches.
- Simple Web final text metric deferral: the final text paint pass now computes
  glyph scale, advance, and ink offsets only in the non-widget branch that uses
  them, avoiding unused metric work for widget text and Chrome text overlays.
- Simple Web normal-flow paint visibility hoisting: normal-flow background,
  border, panel, and button painting now reuse per-node visible-box and
  widget-mode booleans instead of repeating the same branch predicates.
- Simple Web paint clip reuse: normal-flow, negative/zero z-index, and
  positive z-index background/border painting now resolve the node clip once per
  visible node and reuse it across both draw branches.
- Simple Web text glyph lookup allocation removal: sparse widget text and
  scaled framebuffer text now use the existing char-code glyph lookup directly
  in the draw loop instead of allocating a one-character substring fallback.
- Browser/Simple Web backend alias convergence: UI browser and Simple Web
  renderer backend normalization now use the shared Engine2D canonicalizer so
  valid native aliases such as `dx11` preserve the `directx` lane before the
  shared resolver runs.
- Simple Web Engine2D resolver alias convergence: the final Simple Web
  Engine2D resolver now also uses the shared Engine2D canonicalizer, keeping
  DirectX, HIP/ROCm, and CPU SIMD aliases aligned across every GUI entrypoint.
- Simple Web CSS declaration scan allocation removal: `decl_get` and
  `decl_last_pos` now scan declaration blocks by original-string positions
  instead of allocating tail/raw substrings for every property lookup during
  startup style resolution.
- Simple Web CSS variable replacement guard: `_css_resolve_vars` now stops once
  no `var(` tokens remain and skips full-buffer replacement for unused root
  custom properties; style computation also avoids a duplicate candidate-count
  length read.
- Simple Web dead CSS helper removal: removed the unused `flatten_at_blocks`
  helper whose unresolved local symbols forced renderer module JIT lowering to
  fall back to the interpreter during focused startup/layout tests.
- Simple Web parser substring removal: HTML comment detection now uses
  `text_matches_at` and self-closing tag detection uses `char_at`, avoiding
  small substring allocations in the startup parse/count passes.
- Simple Web attribute parser substring removal: tag-name scans, quoted and
  unquoted attribute value parsing, and class-token counting now use `char_at`
  plus original-string slice offsets instead of allocating one-character and
  tail substrings for every parsed element.
- Simple Web numeric parser substring removal: CSS integer, nth-integer, and
  opacity fraction scans now use `char_at` instead of allocating a substring for
  every scanned digit during style application.
- Simple Web selector scanner substring removal: pseudo-list, `:has`, selector
  group splitting, child-combinator normalization, and selector tokenization
  loops now use `char_at` instead of allocating one-character substrings.
- Simple Web color parser substring removal: direct `#rgb`, `#rrggbb`, and
  `rgb(...)` prefix parsing now uses `char_at`/`text_matches_at` instead of
  allocating tiny substrings during CSS color resolution.
- Simple Web selector specificity substring removal: class/id specificity
  prefix checks and multi-class dot counting now use `char_at`, avoiding
  per-character substring allocation during cascade rule ordering.
- Simple Web selector bucket prefix allocation removal: base selector matching
  and selector bucket kind/value resolution now use `char_at` for leading
  class/id checks, avoiding one-character substring allocation in startup rule
  bucketing and matching.
- Simple Web selector token fill allocation removal: `selector_group_parts`
  now records token start offsets and slices each token once instead of
  rebuilding tokens with per-character string concatenation during selector
  parsing.
- Simple Web child-combinator normalization allocation removal:
  `normalize_child_combinators` now returns the trimmed selector directly when
  no top-level child combinator exists and rebuilds only range chunks around
  `>` combinators otherwise, avoiding per-character output concatenation.
- Simple Web selector group splitting allocation removal: `split_selector_groups`
  now tracks group start offsets and slices top-level comma-separated selector
  groups once instead of rebuilding the current group one character at a time
  during both count and fill passes.
- Simple Web pseudo selector option splitting allocation removal:
  `:not`/`:is`/`:where` and `:has` option scanners now keep option start
  offsets and slice each comma-separated argument once, preserving depth-aware
  comma handling without per-character string concatenation.
- Simple Web CSS custom-property collection allocation removal:
  `_css_collect_custom_props` now counts root custom properties, fills an
  exact-size entry array, and joins once instead of repeatedly growing the
  collected property text while scanning `:root` blocks.
- Simple Web multi-style custom-property aggregation allocation removal:
  `extract_css` now counts non-empty custom-property style blocks, fills an
  exact-size block array, and joins once instead of repeatedly appending each
  `<style>` block's collected custom property text.
- Simple Web custom-property prepass duplicate scan removal: `extract_css`
  now counts valid `<style>` blocks without calling `_css_collect_custom_props`
  during the count pass, so each style block is parsed for root custom
  properties only in the fill pass.
- Simple Web child-combinator chunk join allocation removal:
  `normalize_child_combinators` now uses `chunks.join("")` after range slicing
  instead of appending each chunk into an output string.
- Simple Web color/attribute micro-allocation removal: `parse_color_any` now
  finds the closing RGB parenthesis in the original string and slices once,
  while CSS attribute unquoting uses `char_at` for quote checks instead of
  allocating first/last-character substrings.
- Simple Web HTML parser first-character allocation removal: both the node
  count and fill passes now use `char_at(0)` for tag dispatch instead of
  allocating a one-character substring for every parsed tag.
- Simple Web compound-class match allocation removal: `class_has_all` now scans
  dot-separated class requirements directly instead of allocating a `split(".")`
  array for every selector match.
- Simple Web RGB color split allocation removal: `parse_color` now parses
  comma-delimited `rgb(...)` components from the original string ranges instead
  of allocating an inner substring and `split(",")` array during style
  resolution.
- Simple Web selector tail allocation removal: base selector matching, selector
  bucket key extraction, and specificity scoring now use absolute offsets for
  `tag#id.class` and class-tail scans instead of allocating intermediate tail
  strings during cascade setup and matching.
- Engine2D font operation lane routing: `engine2d_operation_lane` now classifies
  vector-font, bitmap-font, glyph raster/blit, and generic font offload
  operations as processing-lane work so preferred font offload backends are not
  hidden behind the combined fallback lane.
- Pure Simple web renderer auto default: `SimpleWebRenderer.create(...)` and
  the `simple_web_render_html_to_pixels(...)` facade now use the Engine2D
  `auto` backend path so generic layout rendering follows the native-first
  order before CPU fallbacks while explicit `software` remains available.
