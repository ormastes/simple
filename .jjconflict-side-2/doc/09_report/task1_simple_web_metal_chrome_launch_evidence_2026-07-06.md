# Task #1 — Simple Web browser: Simple-2D(Metal) + Chrome launch, Metal device-readback proof, cross-backend comparison

- Date: 2026-07-06
- Host: macOS (Darwin), aarch64-apple-darwin, Apple M4
- Repo commit run against: `515600c7e9a8d331398730a7f880b7b424f51f4d`
- Vehicle: deployed self-hosted `bin/simple` -> `release/aarch64-apple-darwin-macho/simple`
- HARD RULE honored: zero source-code edits; evidence artifacts + this report only.

## Result summary

| Deliverable | Status |
|---|---|
| 1. Simple-2D Metal launch + render-log capture (snapshot lane) | PASS |
| 1. Real window (`--open`) lane | BLOCKED (winit extern missing in deployed binary) |
| 2. Chrome backend lane render + capture | PASS |
| 3. Real-GPU proof for Metal (device_readback + gpu_frame_complete) | PASS |
| 4. Cross-backend comparison (checksum + pixel diff) | PASS — bit-exact |
| 5. Evidence bundle + report | PASS |

## Harness reused (not reinvented)

`scripts/check/check-macos-metal-browser-backing-evidence.shs` — the existing tri-lane
(simple-metal / chrome / electron) harness at 320x240 on `test/fixtures/pixel_compare/css_boxes.html`.
It runs `tools/pixel_compare/render_simple_html.spl` (PIXEL_BACKEND=metal) for the Simple lane,
`tools/chrome-live-bitmap/capture_html_argb.js` for Chrome, and
`tools/electron-live-bitmap/capture_html_argb.js` for Electron, then computes per-lane ARGB
checksum + pairwise bit diff. Exit 0 (both `browser_backing_status` and
`pixel_comparison_status` = pass).

Reproduction:
```
SIMPLE_EXECUTION_MODE=interpret sh scripts/check/check-macos-metal-browser-backing-evidence.shs
```

## LANE Simple-2D / Metal (snapshot/readback — pixel evidence lane)

- Launch cmd (as driven by harness):
  `PIXEL_HTML=test/fixtures/pixel_compare/css_boxes.html PIXEL_W=320 PIXEL_H=240 PIXEL_BACKEND=metal PIXEL_OUT=build/macos-metal-browser-backing/simple.argb.json SIMPLE_LIB=src bin/simple run tools/pixel_compare/render_simple_html.spl --mode=interpreter`
- Readback source label: **`device_readback`** (typed `ReadbackSource.DeviceReadback`).
- `gpu_backend_used=true`; `requested_backend=metal`; `resolved_backend=metal`;
  producer=`simple-web-core-renderer-metal-gpu-readback`.
- gpu_frame_complete probe fired: **YES** (implied and required). `device_readback` is only
  emitted by `MetalBackend.read_pixels_with_source()` when `self.gpu_frame_complete` is true
  and `read_pixels_gpu_only()` downloads the full surface from the real GPU device buffer
  (`metal_buffer_download_ptr` on `self.d_framebuffer`) —
  `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:423-428, 445-481`. A false probe would
  have fallen to `cpu_mirror` (CpuMirror). It did not.
- Checksum: **329775811848360** (nonblank 76800/76800).
- Metal render log: `build/macos-metal-browser-backing/simple-render.log`. There is NO separate
  per-dispatch Metal command-log artifact on this present path
  (`present_layout_pixels_with_engine2d_readback`, which css_boxes routes through — the
  `[web-gpu-paint]` dispatch line only fires on the `present_gpu_paint_readback` path used by
  `display:contents` content). The render log's closing provenance line is the Metal evidence:
  ```
  [render_simple_html] wrote build/macos-metal-browser-backing/simple.argb.json width=320 height=240 nonblank=76800 requested_backend=metal resolved_backend=metal engine2d_readback_source=device_readback gpu_backend_used=true
  ```
- Window opened (`--open`): **NO — blocked** (see Blockers).

## LANE Chrome (and Electron)

- Chrome cmd (harness): `CHROME_CAPTURE_HTML=... CHROME_CAPTURE_WIDTH=320 CHROME_CAPTURE_HEIGHT=240 CHROME_CAPTURE_DISABLE_GPU=false node tools/chrome-live-bitmap/capture_html_argb.js`
- Chrome checksum: **329775811848360**; capture: `build/macos-metal-browser-backing/chrome.argb.json`;
  proof: `build/macos-metal-browser-backing/chrome-proof.json`.
- Chrome GPU backing: metal-backed — `gpu_compositing=enabled`, `display_type=ANGLE_METAL`,
  `skia_backend_type=Metal`, `gl_renderer=ANGLE (Apple, ANGLE Metal Renderer: Apple M4, ...)`.
- Electron checksum: **329775811848360**; capture: `electron.argb.json`; also ANGLE_METAL / Apple M4,
  `capture_compositor_mode=offscreen-osr-exact-srgb`, `offscreen_paint=true`.

## COMPARISON

- simple (metal device_readback) = chrome = electron = **329775811848360**, all 320x240, 76800 nonblank.
- Pairwise ARGB bit diff (`pairwise-argb-diff`): electron↔chrome = pass, electron↔simple = pass,
  chrome↔simple = pass. **Bit-exact, mismatch count 0.** No AA/structural diff to classify.

## Evidence bundle

- Per-run bundle (standard gate location): `build/macos-metal-browser-backing/`
  - `evidence.env` (schema keys `macos_metal_*`), `report.md`
  - `simple.argb.json`, `chrome.argb.json`, `electron.argb.json`
  - `chrome-proof.json`, `electron-proof.json`, `chrome-source.env`, `electron-source.env`, `chrome-geometry.json`
  - `simple-render.log`, `chrome-capture.log`, `electron-capture.log`
- Rollup schema/bundle gate: `scripts/check/check-gui-web-2d-platform-evidence-bundle.shs`
  (freshness + schema-key validation over per-lane evidence.env files).
- This report: `doc/09_report/task1_simple_web_metal_chrome_launch_evidence_2026-07-06.md`.

## Blockers (for orchestrator delegation)

1. Real window `--open` lane cannot launch through the deployed self-hosted binary.
   - Command: `SIMPLE_EXECUTION_MODE=interpret SIMPLE_LIB=src bin/simple src/app/ui.browser/main.spl examples/06_io/ui/hello_web.ui.sdn --open --backend=metal`
   - Error: `error: semantic: unknown extern function: rt_winit_event_loop_new`
   - Call site: `src/app/ui.browser/app.spl:16` (extern decl) and `:30` (call, via
     `run_browser_gui_with_access_store`).
   - Root cause: the extern IS implemented in the seed interpreter
     (`src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/winit_sffi_window.rs:18`),
     but the deployed self-hosted `bin/simple` (release/aarch64-apple-darwin-macho/simple) was
     built from a runtime that does not register the winit event-loop extern family. This is the
     known stage-4 redeploy architectural block
     (`doc/08_tracking/bug/bootstrap_stage4_graph_load_timeout_2026-07-05.md`), NOT a source
     defect. NO code edit is warranted here.
   - Proposed fix (delegate): redeploy a self-hosted `bin/simple` whose embedded runtime registers
     `rt_winit_event_loop_new` and the winit window/event externs (unblock stage-4 graph-load
     timeout), then re-run the `--open` command above. Pixel/GPU evidence is fully covered by the
     snapshot/device_readback lane in the meantime, so this blocker gates only the on-screen
     window, not GPU correctness.

## Notes / honesty

- The Simple lane render emits deprecation warnings (`[...]`→`<...>` generics) and
  `[gc-warning] higher_layer_runtime_family` lines; both are non-fatal and did not affect pixels.
- The `--mode=interpreter` FLAG works for this buffer-render (non-window) path; the env var
  `SIMPLE_EXECUTION_MODE=interpret` was also exported. The window-lane crash is an extern-registry
  gap, unrelated to the Cranelift ARM64 far-branch mode issue.

## Follow-up: WM showcase event handling lesson

The hosted WM showcase count-up path works when the app is treated as a real child process, not
as embedded WM code:

- The WM launches `examples/06_io/ui/widget_showcase_gui.spl` from the filesystem through
  `bin/simple run ...` with WM bridge environment variables.
- The WM converts host pointer input into filesystem event records with monotonically increasing
  `seq` values (`down`, `up`, `move`, and `tick`) and writes both the current event file and the
  per-sequence event file.
- The child app drains queued event records in order, applies them through the same Simple UI
  state transition used by the native showcase (`showcase_on_pointer` / `showcase_on_tick`), then
  writes a new PPM frame, state file, and frame sequence.
- The WM watches the frame sequence and presents only when a new child frame is available or WM
  chrome changed. This is why `button_count` now increments: the click is no longer only a host
  drag/titlebar event; it reaches the child app state machine and is followed by a child frame
  refresh.

Architecture rules from the fix:

- Keep the app source identical. Native launch and WM launch may use different compile/run
  configuration, but the GUI app must remain a normal Simple UI app.
- Do not expose Metal or `rt_*` backend details to the app. The WM and app should use the common
  Simple UI/runtime facades; backend-specific SFFI remains behind the renderer/runtime layer.
- The WM may use a host-present adapter, but it must retain the last good child frame. A transient
  partial PPM read while the child rewrites the frame must not clear the app content area.
- Event forwarding must be sequenced and drainable. One event per poll leaves button/toggle
  interactions feeling hung; draining bounded batches lets click down/up and slider/toggle changes
  settle into one redraw.
- Performance-sensitive WM drawing should avoid full-screen readback loops and repeated large
  array-copy helper returns. Compose chrome and child blits through retained pixel buffers or a
  common backend facade, then present once per dirty frame.
