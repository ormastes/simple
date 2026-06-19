# RenderDoc Capture Infrastructure

Use the shared RenderDoc interface for both capture styles:

```sh
scripts/setup/setup-renderdoc-env.shs --check
scripts/setup/setup-renderdoc-env.shs --register-vulkan-layer
scripts/tool/renderdoc-evidence.shs capture-simple
scripts/tool/renderdoc-evidence.shs capture-html
scripts/tool/renderdoc-evidence.shs capture-electron-html
RDOC_SIMPLE_EVIDENCE_ENV=build/renderdoc/canonical-probe/simple/evidence.env \
  sh scripts/check/check-renderdoc-simple-gate.shs
RDOC_EXTERNAL_RUN_CAPTURE=1 sh scripts/check/check-renderdoc-external-host-capture.shs
RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/renderdoc/canonical-probe/electron-html/evidence.env \
  sh scripts/check/check-renderdoc-electron-html-gate.shs
PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/production_gui_web_renderer_parity_evidence/evidence.env \
  sh scripts/check/check-production-gui-web-renderer-parity-gate.shs
```

## Interfaces

- `scripts/tool/renderdoc-evidence.shs env` prints resolved paths.
- `scripts/tool/renderdoc-evidence.shs capture-simple` runs the Simple
  in-application `rt_renderdoc_*` Vulkan Engine2D capture.
- `scripts/tool/renderdoc-evidence.shs capture-html` runs original
  `renderdoccmd capture` around Chrome for the HTML/CSS fixture.
- `scripts/tool/renderdoc-evidence.shs capture-electron-html` runs original
  `renderdoccmd capture` around Electron's bundled Chromium for the HTML/CSS
  fixture.
- `test/helpers/renderdoc_capture_helper.shs` exposes the same interface for
  test scripts.

Compatibility wrappers remain:

- `scripts/check/check-renderdoc-vulkan-capture.shs`
- `scripts/check/check-renderdoc-html-capture.shs`
- `scripts/check/check-renderdoc-electron-html-capture.shs`

## Environment

Common variables:

- `RDOC_HOME`: RenderDoc install root containing `bin/renderdoccmd`.
  On macOS, this may also be a `RenderDoc.app` bundle containing
  `Contents/MacOS/renderdoccmd`.
- `RDOC_CHROME`: Chrome/Chromium binary for HTML capture. If unset, the helper
  checks common Playwright/Linux Chrome paths and macOS app bundles such as
  `/Applications/Google Chrome.app/Contents/MacOS/Google Chrome`.
- `RDOC_ELECTRON`: Electron binary for Electron HTML capture. If unset, the
  helper checks the repo-local `tools/electron-shell/node_modules` install.
- `RDOC_OUTPUT_DIR`: base output directory.
- `RDOC_CAPTURE_TIMEOUT_SECS`: bounded capture timeout.
- `RDOC_HTML_PATH`: HTML fixture for `capture-html`.
- `RDOC_ELECTRON_WIDTH`, `RDOC_ELECTRON_HEIGHT`, `RDOC_ELECTRON_SETTLE_MS`:
  Electron capture viewport and settle controls.
- `RDOC_SIMPLE_PROG`: Simple capture program for `capture-simple`.

The helper validates `.rdc` files by checking the `RDOC` magic header. If a host
cannot provide Chrome Vulkan or a non-CPU Vulkan device, record the concrete
reason in `doc/09_report/` instead of duplicating ad hoc capture commands.

## Evidence Artifacts

Each capture command writes an `evidence.env` file under its output directory.
Important keys:

- `rdoc_backend`: `simple` or `original`.
- `rdoc_scene`: capture scenario name.
- `rdoc_log`: capture log path.
- `rdoc_capture_status`: `pass`, `fail`, or `unavailable`.
- `rdoc_capture_reason`: concrete pass/fail/unavailable reason.
- `rdoc_capture_file`: `.rdc` path when one exists.
- `rdoc_capture_magic`: `RDOC` for a valid RenderDoc capture.
- `rdoc_chromium_requested_api`: requested Chromium graphics API for Electron
  HTML capture. The canonical Electron path records `vulkan`.
- `rdoc_chromium_requested_angle`: requested ANGLE backend for Electron HTML
  capture. The canonical Electron path records `vulkan`.
- `rdoc_chromium_launch_flags`: exact Electron Chromium flags, including
  `--enable-features=Vulkan --use-angle=vulkan`.

If `renderdoccmd` is unavailable, `capture-simple` and `capture-html` still
write an `evidence.env` artifact under the requested output directory with
`rdoc_capture_status=unavailable`,
`rdoc_capture_reason=missing-renderdoc`, an empty `rdoc_capture_file`, and an
empty `rdoc_capture_magic`. This is not completion evidence; it makes the
missing capture explicit for status gates and CI artifacts.
`capture-electron-html` additionally records the HTML fixture path, Electron
binary, capture script, viewport, and requested Vulkan/ANGLE Chromium launch
contract even in this unavailable state, so the remaining missing component is
visible as `renderdoccmd` rather than an ambiguous Electron setup failure.

The top-level GUI RenderDoc feature audit re-emits the HTML/CSS rendering
manifest traceability details from
`scripts/check/check-html-css-rendering-manifest-traceability.shs`, including
the manifest and fixture paths, HTML tag covered/total counts, implemented CSS
property covered/total counts, missing tag/property lists, fixture scene count,
and manifest scenes missing fixture HTML. A restart audit should therefore show
the 105/105 HTML tag coverage and 62/62 implemented CSS property coverage in
the same evidence env as the Simple, original Chrome, Electron, and production
parity gates.

The nested HTML/CSS RenderDoc goal status gate reports every unsatisfied
RenderDoc goal lane through `renderdoc_goal_blocked_gates` and
`renderdoc_goal_blocked_gate_count`. The top-level GUI audit re-emits those
fields and reports the full completion list through `blocked_completion_gates`
and `blocked_completion_gate_count`, while retaining `blocked_completion_gate`
as the first outstanding gate for older consumers. The top-level list is derived
from the nested Simple/original Chrome RenderDoc lanes, Electron
Chromium/Vulkan RenderDoc gate, and the production GUI/web parity gate, so
concurrent missing captures are not hidden by a single status reason.

The current canonical evidence contract is:

- Simple in-application path:
  `build/renderdoc/canonical-probe/simple/evidence.env` must report
  `rdoc_backend=simple`, `rdoc_scene=vulkan-engine2d`,
  `rdoc_program=src/app/test/renderdoc_vulkan_capture.spl`,
  `rdoc_capture_status=pass`, `rdoc_capture_magic=RDOC`, and an existing
  `.rdc` file. The aggregate RenderDoc goal requires this through
  `scripts/check/check-renderdoc-simple-gate.shs`; if that env/file is missing
  or not the Simple Vulkan Engine2D probe path, the GUI RenderDoc goal remains
  incomplete. The top-level GUI RenderDoc feature audit re-emits the Simple
  evidence env, capture status/magic/file, gate status/reason, and required
  backend/scene/program/status/magic fields so the Simple Vulkan requirement is
  visible without opening the nested goal report.
- Original Chrome HTML/CSS path:
  `build/renderdoc/canonical-probe/html/evidence.env`, or an external-host
  evidence env, must pass the original-backend gate with `rdoc_scene=html-css-chrome`,
  `RDOC` magic, and an `rdoc_html_path` ending in
  `test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html`. A local
  failed capture or missing env is not completion evidence. The external-host
  wrapper records the raw capture env, status/reason, `.rdc` file, magic, and
  HTML fixture beside the gate result. The top-level GUI RenderDoc feature
  audit re-emits those fields plus the required backend/scene/status/magic and
  fixture suffix fields so the original Chrome/Vulkan requirement is visible
  beside the Simple and Electron lanes.
- Electron Chromium HTML/CSS path:
  `build/renderdoc/canonical-probe/electron-html/evidence.env` should report
  `rdoc_backend=electron`, `rdoc_scene=html-css-electron`,
  `rdoc_capture_status=pass`, `rdoc_capture_magic=RDOC`,
  `rdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html`,
  `rdoc_electron_capture_script=tools/electron-live-bitmap/capture_html_argb.js`,
  `rdoc_chromium_requested_api=vulkan`,
  `rdoc_chromium_requested_angle=vulkan`, launch flags containing
  `--enable-features=Vulkan` and `--use-angle=vulkan`, and an existing `.rdc`
  file when proving the Electron-backed GUI path. The GUI RenderDoc feature
  audit requires this through
  `scripts/check/check-renderdoc-electron-html-gate.shs` before it can report
  `pass`, and re-emits the Electron gate source env, captured file/magic,
  fixture path, Electron binary, capture script, requested Vulkan/ANGLE fields,
  and launch flags.
- Production GUI/web renderer parity path:
  `build/production_gui_web_renderer_parity_evidence/evidence.env` must report
  the top-level parity status and component statuses as `pass`, including the
  renderer matrix, 50-case layout manifest, Tauri/Chrome surface manifest,
  backend parity, font offload/readback, and raw Metal framebuffer readback.
  The Tauri/Chrome surface manifest must prove live Electron, Tauri, and
  Chrome captures, 50 Tauri and 50 Chrome cases, 36 pass cases plus 14 tracked
  divergence cases for each browser surface, 0 fail cases, 0 mismatch counts,
  `no_fake_capture=true`, and `blur_or_tolerance_used=false`.
  The GUI RenderDoc feature audit requires this through
  `scripts/check/check-production-gui-web-renderer-parity-gate.shs` before it
  can report `pass`; missing parity evidence is not treated as optional.

## External Host Gate

Use the gate when another host or CI job supplies the original
RenderDoc+Chrome evidence:

```sh
RDOC_EXTERNAL_RUN_CAPTURE=1 sh scripts/check/check-renderdoc-external-host-capture.shs

RDOC_HTML_EVIDENCE_ENV=build/renderdoc/canonical-probe/html/evidence.env \
  sh scripts/check/check-renderdoc-html-external-host-gate.shs
```

The external-host wrapper runs setup, capture, and the gate. The low-level gate
passes only when the source evidence contains:

- `rdoc_backend=original`
- `rdoc_scene=html-css-chrome`
- `rdoc_capture_status=pass`
- `rdoc_capture_magic=RDOC`
- `rdoc_html_path` ending in
  `test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html`
- an existing `.rdc` path in `rdoc_capture_file`

Otherwise it writes fail-closed evidence under
`build/renderdoc/html-external-host-gate/evidence.env`.

Without `RDOC_EXTERNAL_RUN_CAPTURE=1`, the wrapper performs a readiness-only
run and writes `rdoc_external_host_capture_status=unavailable` with
`rdoc_external_host_capture_reason=capture-not-requested`.

## Simple Vulkan Gate

Use the Simple gate when the canonical Simple in-application capture or a CI
host supplies the Simple Vulkan `.rdc`:

```sh
RDOC_OUTPUT_DIR=build/renderdoc/canonical-probe \
  scripts/tool/renderdoc-evidence.shs capture-simple

RDOC_SIMPLE_EVIDENCE_ENV=build/renderdoc/canonical-probe/simple/evidence.env \
  sh scripts/check/check-renderdoc-simple-gate.shs
```

The gate passes only when the source evidence contains:

- `rdoc_backend=simple`
- `rdoc_scene=vulkan-engine2d`
- `rdoc_program` ending in `src/app/test/renderdoc_vulkan_capture.spl`
- `rdoc_capture_status=pass`
- `rdoc_capture_magic=RDOC`
- an existing `.rdc` path in `rdoc_capture_file`

Missing RenderDoc, non-Simple backend evidence, wrong scene/program metadata,
or a missing `.rdc` file all keep the gate out of `pass`.

## Electron Chromium/Vulkan Gate

Use the Electron gate when the canonical Electron capture or a CI host supplies
the Electron-backed HTML/CSS `.rdc`:

```sh
RDOC_OUTPUT_DIR=build/renderdoc/canonical-probe \
  scripts/tool/renderdoc-evidence.shs capture-electron-html

RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/renderdoc/canonical-probe/electron-html/evidence.env \
  sh scripts/check/check-renderdoc-electron-html-gate.shs
```

The gate passes only when the source evidence contains:

- `rdoc_backend=electron`
- `rdoc_capture_status=pass`
- `rdoc_capture_magic=RDOC`
- `rdoc_chromium_requested_api=vulkan`
- `rdoc_chromium_requested_angle=vulkan`
- an existing `.rdc` path in `rdoc_capture_file`

Missing RenderDoc, missing Electron capture output, non-Electron backend
evidence, or non-Vulkan Chromium request metadata all keep the gate out of
`pass`.

## macOS Notes

macOS does not provide native Vulkan drivers. Use the LunarG Vulkan SDK with
MoltenVK, or another Metal-backed Vulkan portability implementation, when
testing the Simple Vulkan path on macOS.

The setup helper resolves either an unpacked RenderDoc tree with
`bin/renderdoccmd` or a macOS `RenderDoc.app` bundle, and prints both
`LD_LIBRARY_PATH` and `DYLD_LIBRARY_PATH` exports for prepared capture hosts.

The shared CLI remains the preferred interface:

```sh
scripts/setup/setup-renderdoc-env.shs --check
scripts/tool/renderdoc-evidence.shs capture-simple
scripts/tool/renderdoc-evidence.shs capture-html
sh scripts/check/check-renderdoc-macos-portability-probe.shs
```

Treat macOS results as portability evidence unless they produce the same
original RenderDoc+Chrome `.rdc` contract required by
`scripts/check/check-renderdoc-html-external-host-gate.shs`. If Chrome renders
through Metal/ANGLE or Vulkan-over-Metal, record that distinction in
`doc/09_report/`. Use Xcode GPU Frame Capture for Metal-level inspection when
RenderDoc cannot capture the macOS path.

By default the macOS probe records availability only. Set
`RDOC_MACOS_RUN_CAPTURES=1` on a prepared macOS host to run the Simple
RenderDoc capture and exploratory Chrome capture through the shared CLI.
