# MDI And Chromium Layout Parity Work Orders

Date: 2026-06-11
Status: Active scoped work orders

## Goal

Prove and harden the requested GUI stack:

- Pure Simple web renderer shows the shared MDI windows.
- Events route through the window manager and GUI bridge, including click,
  focus, drag, button, titlebar, and text input paths.
- Titlebar text, buttons, input, and CSS styling work on Linux, macOS, and
  Windows, with explicit skip reasons only where the host is unavailable.
- Chromium layout comparison uses real browser layout/capture evidence and
  drives Simple layout toward matching item size, boundary, and position.

## Non-Negotiable Rules

- Do not use blur, tolerance, resolution downscaling, or fuzzy pixel matching
  to claim parity.
- Do not paste captured Chromium pixels into the renderer or add
  fixture-specific overlay corrections.
- Treat text glyph antialiasing as incomplete until a generic text
  metric/raster/compositing path proves it with current live evidence.
- Preserve unrelated dirty files from other agents; each work order owns only
  the paths listed under its lane.

## Current Evidence Snapshot

- `origin/main` at `e570ff72e763` includes the latest pushed live browser event,
  computed-style, QMP drag-gate, and multicore green follow-up evidence.
- Generated-GUI Electron matrix is exact at `80x64`, `96x72`, `128x96`, and
  `160x120`.
- Electron layout manifest has 18 rows: 16 exact, 2 tracked text divergences,
  0 failures.
- Aggregate production parity still fails because live Chrome text cases are
  divergent: `text_raster_track` mismatch count `1292` and
  `line_height_text_track` mismatch count `493`.
- The remaining text delta is real: Chrome uses browser font metrics,
  baseline/ascent/descent placement, shaping, and antialiasing while Simple
  still uses an integer-scaled 5x7 bitmap font for this path.
- MDI lifecycle/render evidence exists through
  `test/03_system/gui/gui_entry_engine2d_wm_simple_web_spec.spl` and related
  reports, but full titlebar/input/drag event proof is still partial:
  `test/03_system/gui/wm_input_qemu_smoke_spec.spl` contains the right markers
  but can route through a linker-blocker branch on some hosts.
- Browser-side source-contract evidence now covers canonical widget
  pointer/text input forwarding, MDI titlebar drag focus/move commands,
  traffic-light close/minimize/maximize commands, and title-command input
  routing through `test/02_integration/app/ui.web/wm_bridge_test.spl`.
- Pure Simple shared-MDI source evidence now covers the actual Terminal window
  HTML emitted by `src/app/ui_shared_mdi/main.spl`:
  `test/03_system/gui/ui_shared_mdi_titlebar_widget_spec.spl` imports
  `shared_mdi_terminal_window_html()` and asserts the shared renderer source
  contains the title text, titlebar widget slot, titlebar `Run` button
  `data-simple-titlebar-widget="button"`, `data-action="mdi_terminal_action"`,
  body `Run` button, body input `data-target-id="mdi_terminal_input"`,
  `value="ready"`, and the CSS hook
  `.simple-titlebar-widget{background:rgb(18,58,52);border-color:rgb(52,211,153);color:rgb(236,254,255);}`.
  This proves the shared MDI app source carries the requested button/input/CSS
  hooks before host-shell rendering.
- Live Chromium browser evidence now runs through
  `scripts/check/check-wm-browser-event-routing-evidence.shs`: it loads the real
  `src/app/ui.web/wm.js`, opens an MDI window through the Electron IPC path,
  simulates titlebar drag, traffic-light maximize, title-command Enter, body
  text input, and body pointer down/up, then asserts the emitted `window_cmd`
  and `input_event` frames. The same live Chromium pass now also checks
  `getComputedStyle` evidence for title text, three traffic-light buttons,
  titlebar height/display/cursor/background, and title-command input
  min-width/height/background/cursor. The 2026-06-11 report now exposes the
  actual routed payloads as evidence: `move_payload_window_id_hint=win1`,
  `move_payload_source=native_event`, `move_payload_x=86`,
  `move_payload_y=86`, `expected_move_x=86`, `expected_move_y=86`,
  `title_command_text=/tmp/project`, and
  `text_input_text=Hello Simple`, plus exact traffic-light colors
  `rgb(239, 68, 68)`, `rgb(234, 179, 8)`, and `rgb(34, 197, 94)`.
  This is not a substitute for the remaining SimpleOS QEMU framebuffer
  click/drag proof or the separate Linux-native host backend semantic
  event+style proof.
- `test/03_system/gui/gui_entry_engine2d_wm_simple_web_spec.spl` now contains a
  fail-closed QMP drag-delta gate: it captures the BGA framebuffer with
  `pmemsave`, injects deterministic HMP `mouse_move`/`mouse_button` events, then
  requires a second framebuffer capture to differ by real bytes before passing.
  This is a gate, not completed proof yet: the focused SSpec runner currently
  fails before listing the scenario for both the modified file and the
  origin-baseline copy, so live QEMU click/drag proof remains blocked on the
  runner/import path or a standalone QMP wrapper.
  Residual risk: the current gate checks a global framebuffer delta rather than
  a drag-region-specific movement signature, so later work should tighten it
  after the runner path executes reliably.
- `scripts/check/check-simpleos-wm-qmp-drag-delta-evidence.shs` is the current
  standalone live wrapper for the same host-QMP path. It runs the root-level
  `simpleos_desktop_qmp_launch_root.spl` launcher because the same launcher shape
  is path-sensitive under `src/app/test` and exits `139` there. With the
  `examples/09_embedded/simple_os` submodule initialized and `SIMPLE_BINARY`
  propagated from `SIMPLE_BIN`, the wrapper rebuilds
  `gui_entry_engine2d.spl`, launches QEMU, verifies the MDI/WM/Web marker set,
  captures before/after BGA frames with QMP `pmemsave`, injects HMP mouse drag
  events, and requires both global byte deltas and source/destination
  drag-region deltas. The current 2026-06-11 result is intentionally failing:
  launcher status is `pass`, all marker state fields are true, but
  `changed_bytes=0`. A focused `simple_os` submodule attempt now initializes
  PS/2 auxiliary mouse reporting inside `gui_entry_engine2d.spl` and waits for
  real packets before re-rendering a dragged browser window. The guest reports
  `[host-input] no-host-mouse-packets` for `q35` + HMP mouse events, `pc` + HMP
  mouse events, and `q35` + QMP `input-send-event`, so host-QMP mouse input is
  still not reaching the guest input path.
  Timing review update (2026-06-11): the guest PS/2 polling window was extended
  from `1500000` to `20000000` loop iterations and now emits
  `[host-input] poll-window-start` / `[host-input] poll-window-end` markers. The
  strict wrapper captured the after-frame while the log showed
  `[host-input] poll-window-start` and no poll-window end, yet still measured
  `changed_bytes=0` with identical before/after hashes. This makes a missed
  guest polling window unlikely; the remaining failure is that injected host
  pointer events are not delivered to the guest-visible input device path.
  Bugs:
  `doc/08_tracking/bug/simpleos_wm_qmp_source_target_missing_2026-06-11.md` and
  `doc/08_tracking/bug/simpleos_wm_host_qmp_mouse_input_no_framebuffer_delta_2026-06-11.md`.
- Windows and macOS live evidence is host-gated today:
  `test/03_system/gui/windows_native_mdi_evidence_spec.spl` reports
  `requires-windows` off Windows, and
  `test/03_system/gui/macos_gui_live_window_evidence_spec.spl` reports
  `requires-macos` off macOS.
- The generated-spec layout guard currently reports `0` executable
  `*_spec.spl` files under `doc/06_spec`.

## Chromium Research Baseline

- Chromium's current layout architecture is LayoutNG/RenderingNG, not the
  older legacy layout engine. The relevant external references are:
  - https://developer.chrome.com/docs/chromium/renderingng-architecture
  - https://developer.chrome.com/docs/chromium/layoutng
  - https://www.chromium.org/blink/layoutng/
  - https://chromium.googlesource.com/chromium/src/third_party/+/refs/heads/main/blink/renderer/core/layout/layout_ng.md
- The practical parity target for Simple is a browser-like pipeline:
  style resolution, layout geometry, paint, then compositing. The first
  implementation win should compare layout geometry through live Chromium DOM
  rect/computed-style extraction before trying to solve glyph antialiasing.
- LayoutNG uses a physical fragment tree for paint and hit-testing. Simple's
  box tree can still converge incrementally by recording equivalent per-item
  fragment geometry: content box, padding box, border box, paint clip, stacking
  order, and hit rect.
- Current repo access paths:
  - `tools/electron-live-bitmap/capture_html_argb.js` already extracts
    `[data-geom-label]` DOM geometry through Electron/Chromium, including
    border-box `x`/`y`/`width`/`height`, computed padding, computed border
    widths, background color, and normalized text.
  - `src/app/wm_compare/electron_geometry_compare.spl` parses that geometry
    into `StructuralLayoutBox` for structured comparison. The structural box
    comparison now treats padding, border, and background differences as exact
    layout mismatches rather than pixel-only metadata.
  - `tools/chrome-live-bitmap/capture_html_argb.js` captures real Chrome ARGB
    screenshots and now exports matching `chrome-headless-geometry` DOM
    geometry with the same style-box schema when
    `CHROME_CAPTURE_GEOMETRY_OUTPUT` is set.
  - `scripts/check/check-chrome-simple-web-layout-bitmap-evidence.shs` records
    the Chrome geometry artifact beside the ARGB proof and fails closed if a
    successful Chrome capture does not write it.
  - `test/03_system/gui/wm_compare/famous_site_corpus_spec.spl` validates
    stored Chrome metrics for corpus fixtures, including text rect/line data.
- Live sanity evidence (2026-06-11): Chrome headless geometry capture for
  `test/fixtures/html_compat/02_block_boxes.html` produced 6 labeled items and
  `src/app/wm_compare/html_compat_geometry_probe_cli.spl` reported
  `layout_match` with `mismatch_count=0` against Simple structural boxes.
- Schema evidence (2026-06-11):
  `test/03_system/gui/wm_compare/electron_geometry_compare_spec.spl` proves the
  shared Chrome/Electron geometry parser preserves padding, border, and
  background fields, and that exact comparison fails closed on a border-width
  mismatch without blur, tolerance, downscaling, or text-antialiasing work.
- Live Chrome schema smoke (2026-06-11):
  `doc/09_report/chrome_geometry_style_box_schema_evidence_2026-06-11.md`
  records a real Chrome headless capture for
  `test/fixtures/html_compat/07_scrollable_list.html`; it wrote
  `chrome-headless-geometry` with computed padding and background fields and
  kept `blur_or_tolerance_used=false`.
- Manifest geometry evidence (2026-06-11):
  `scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs`
  captured real Chrome headless geometry for 21 supported `html_compat`
  fixture rows and compared exact Simple structural boxes for border-box rects,
  computed padding, border widths, and background color. Report:
  `doc/09_report/chrome_html_compat_geometry_manifest_evidence_2026-06-11.md`;
  result `status=pass`, `pass_count=21`, `fail_count=0`,
  `blur_or_tolerance_used=false`.
- Famous-site corpus div geometry evidence (2026-06-11):
  `test/03_system/gui/wm_compare/structural_layout_report_spec.spl` now checks
  `build_site_corpus_div_geometry_report` for `site_0_google` and
  two bounded six-row summary chunks for the first twelve deterministic corpus
  rows against stored Chrome metrics. The full-corpus wrapper
  `scripts/check/check-famous-site-corpus-div-geometry-chunks.shs` now runs the
  same exact div geometry comparison across all 132 deterministic corpus rows
  in 22 separate six-row Simple processes. The full report is
  `doc/09_report/famous_site_corpus_div_geometry_chunks_2026-06-11.md` and
  records `status=pass`, `corpus_count=132`, `chunk_count=22`,
  `pass_count=22`, `fail_count=0`, `blur_or_tolerance_used=false`. This is full
  deterministic corpus div-box evidence, not live-site coverage and not text
  raster parity.

## Agent A: MDI Render And Event Evidence

Ownership:

- `test/03_system/gui/`
- `scripts/check/check-*mdi*.shs`
- `src/lib/common/ui/window*.spl`
- `src/app/ui.web/wm*.spl`
- `src/os/compositor/wm*.spl`
- generated/manual docs directly tied to any changed specs

Small tasks:

1. Inventory existing MDI render, titlebar, input, and WM event evidence.
2. Add or extend a focused scenario that proves pointer down/move/up changes a
   window position through the real bridge, not a static mock.
3. Add or extend a focused scenario that proves titlebar button click and body
   text input dispatch through the real WM/GUI path.
4. Reduce the `wm_input_qemu_smoke_spec.spl` linker-blocker escape hatch so it
   cannot silently stand in for event proof on supported hosts.
5. Generate or refresh the matching `doc/06_spec/...md` manual and review the
   step text.

Exit gate:

- Linux evidence passes locally, and macOS/Windows rows either carry live
  evidence or a precise `requires-macos` / `requires-windows` skip.

## Agent B: Titlebar Styling And Cross-Platform Surface Evidence

Ownership:

- `src/lib/common/ui/html_window.spl`
- `src/os/compositor/wm_scene.spl`
- titlebar/button/input CSS tests under `test/01_unit/` and `test/03_system/`
- platform evidence wrappers under `scripts/check/`

Small tasks:

1. Prove titlebar text, buttons, input, and CSS computed colors/sizes are
   present in structured Draw IR or exact pixel evidence.
2. Separate Linux live evidence from macOS and Windows host-unavailable rows.
3. Add one visible TUI/manual capture reference for titlebar/button/input state
   so the manual can be reviewed without opening source code.

Exit gate:

- Each platform row states `pass`, `fail`, or a host-specific skip with the
  proof path and screenshot/capture path.

## Agent C: Chromium Layout Geometry Access

Ownership:

- `tools/chrome-live-bitmap/`
- `tools/electron-live-bitmap/`
- `test/03_system/gui/wm_compare/`
- `scripts/check/check-*chrome*layout*.shs`
- Chrome metrics/corpus docs under `doc/03_plan/` and `doc/09_report/`

Small tasks:

1. Document the current real Chromium access paths: Chrome ARGB screenshot,
   Electron DOM rects, computed styles, and corpus metrics.
2. DONE (2026-06-11): extend the Chrome and Electron live bitmap runners to
   emit per-element DOM geometry for `[data-geom-label]` nodes, including
   border-box rects, padding, border widths, background, and text.
3. DONE (2026-06-11): add
   `scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs`,
   which emits per-element Chromium DOM geometry for the supported
   `html_compat` manifest rows used by Simple layout and writes per-fixture
   structural reports.
4. DONE (2026-06-11): compare element `x`, `y`, `width`, `height`, border,
   padding, and background without text antialiasing for 21 supported
   `html_compat` manifest rows. Remaining work is broader than this manifest:
   extend equivalent exact geometry/style evidence to larger famous-site corpus
   rows and unresolved browser text/font raster behavior.
5. DONE (2026-06-11): add focused famous-site corpus structural-box evidence
   for the generated `site_0_google` div, fast first-twelve-row SSpec chunks,
   and a full deterministic corpus chunk wrapper using stored Chrome metrics
   and Simple Draw IR. Remaining work is live-site coverage, richer DOM shapes,
   and text/font raster parity.

Exit gate:

- A report lists exact geometry deltas per element for every non-text manifest
  row, with no blur/tolerance or captured-pixel overlay.
- The Chrome and Electron geometry schemas match: `label`, `x`, `y`, `width`,
  `height`, `text`, and later computed style fields.

## Agent D: Simple Layout Algorithm Parity

Ownership:

- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
- focused renderer specs under `test/01_unit/lib/gc_async_mut/gpu/browser_engine/`
- manifest cases and generated docs for changed behavior

Small tasks:

1. Consume Agent C geometry deltas and fix generic layout rules first:
   containing block, display, margin, padding, border, gap, positioned boxes,
   overflow, and visibility.
2. Keep text raster parity separate from box geometry parity.
3. Emit Simple-side `StructuralLayoutBox` geometry for the same manifest labels
   used by Chromium so layout mismatches are caught before pixel comparisons.
4. If text is touched, implement generic font metric/baseline/raster behavior;
   do not add fixture-specific pixel lists.

Exit gate:

- Non-text manifest rows remain exact, new geometry rows improve or pass, and
  text rows remain honestly marked divergent until generic text parity exists.

## Agent E: Verification, Manual, And Sync

Ownership:

- `doc/06_spec/**/*.md`
- `doc/09_report/`
- `doc/03_plan/agent_tasks/mdi_chromium_layout_parity_work_orders.md`
- sync/commit only for the scoped lane

Small tasks:

1. Run `find doc/06_spec -name '*_spec.spl' | wc -l` before each commit.
2. Run the focused specs or wrappers changed by Agents A-D.
3. Regenerate manuals when executable SSpec changes.
4. Commit only scoped files, fetch/rebase with `jj`, and push `main`.

Exit gate:

- The lane has current docs, proof paths, and a pushed commit that excludes
  unrelated dirty files.

## Parallel Order

1. Agents A, B, and C can start immediately and report read-only evidence gaps.
2. Agent D starts after Agent C identifies a geometry delta that is not a text
   raster issue.
3. Agent E runs continuously after any spec or wrapper change.

## Open Blockers

- Full Chrome text pixel parity is not achieved. The known blocker is generic
  browser-font metric, baseline, shaping, and antialiasing parity.
- Whole-corpus div geometry aggregation is not achieved in one Simple process.
  Local probes on 2026-06-11 showed
  `build_site_corpus_div_geometry_summary(7, 160, 120)`, larger limits, and
  unbounded `limit=0` can segfault under `simple run`, while row 6 passes
  individually, two separate six-row chunks pass in SSpec, and the chunked
  wrapper covers all 132 rows by using separate Simple processes. Fix the
  repeated-render/string aggregation runtime crash before promoting a
  full-corpus single-call gate.
- SimpleOS QEMU framebuffer click/drag proof is not achieved yet. The standalone
  QMP wrapper now rebuilds the WM target from source, boots QEMU, and verifies
  all WM/MDI/Web readiness markers, but host-injected HMP mouse drag produces
  `changed_bytes=0` and identical before/after framebuffer hashes. The latest
  guest-side PS/2 polling attempt reports no aux mouse packets across the
  q35/pc/HMP/QMP input matrix, so the next implementation task is to wire a
  supported QEMU pointer device/event path into the SimpleOS WM and make the
  wrapper pass without relaxing the byte/region gates.
- macOS and Windows live platform evidence is not proven from this Linux host;
  host-specific rows must not be promoted without real capture artifacts.
