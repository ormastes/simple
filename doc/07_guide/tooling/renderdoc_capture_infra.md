# RenderDoc Capture Infrastructure

Use the shared RenderDoc interface for both capture styles:

```sh
scripts/setup/setup-renderdoc-env.shs --check
scripts/setup/setup-renderdoc-env.shs --register-vulkan-layer
scripts/setup/setup-gui-web-2d-vulkan-env.shs --check
scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
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
- `scripts/setup/setup-gui-web-2d-vulkan-env.shs` records host readiness and,
  when requested, launches the direct Electron Chromium, Chrome, and Simple
  Engine2D Vulkan probes before optional RenderDoc captures.
- `scripts/setup/setup-gui-web-2d-vulkan-env.ps1` is a deferred Windows
  readiness companion. It is not part of the current top-level GUI/web/2D
  RenderDoc workflow.

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

## GUI/Web/2D Vulkan Setup Probe

The setup probe is the top-level entrypoint for comparing Electron Chromium,
original Chrome, and pure-Simple GUI/web/2D rendering under requested Vulkan.
It writes typed evidence to `build/gui-web-2d-vulkan-env/evidence.env` and
keeps these states separate:

- host Vulkan loader/ICD readiness;
- pixels rendered by Electron or Chrome;
- Chromium logs proving or rejecting ANGLE Vulkan;
- Simple Engine2D Vulkan readback availability;
- optional RenderDoc `.rdc` capture availability and gate status.

Current top-level scope is macOS-only. Use this section to prove and debug the
macOS path now. Do not infer Windows or Linux status from this workflow. Add
Windows and Linux parity capture runbooks later using the same evidence keys
rather than inventing platform-specific status names.

Run a readiness-only probe first:

```sh
scripts/setup/setup-gui-web-2d-vulkan-env.shs --check
```

Run direct launch probes for Electron, Chrome, and Simple Engine2D:

```sh
scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
```

The aggregate status audit keeps readiness and direct launch evidence separate.
`GUI_WEB_2D_VULKAN_ENV` points at the readiness/setup env, while
`GUI_WEB_2D_VULKAN_RUN_EVIDENCE_ENV` can point at a previous `--run`,
`--renderdoc`, or `--renderdoc-simple` env. If unset, the audit looks for
`build/gui-web-2d-vulkan-env-run-auto/evidence.env` and related run dirs. It
emits `gui_web_2d_vulkan_direct_run_source`,
`gui_web_2d_vulkan_direct_run_evidence_env`, and
`gui_web_2d_vulkan_direct_run_mode` before reporting Electron, Chrome, and
Simple runtime fields.

On macOS, the wrapper prefers `src/compiler_rust/target/release/simple` or
`src/compiler_rust/target/debug/simple` when that binary advertises the macOS
Vulkan loader paths (`libvulkan.1.dylib`). The selected executable is recorded
as `gui_web_2d_vulkan_simple_bin`, with the reason in
`gui_web_2d_vulkan_simple_bin_selection_reason`. If no fresh driver exists and
`bin/simple` is older than the Rust runtime changes under test, build the
driver and rerun:

```sh
(cd src/compiler_rust && cargo build --release --bin simple)
scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
```

On a prepared RenderDoc host, debug the supported macOS Simple lane first:

```sh
SIMPLE_BIN=src/compiler_rust/target/release/simple \
  scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc-simple
```

Use the all-lane capture mode only for cross-surface evidence collection:

```sh
scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc
```

For platform package commands without changing the host, print the runbook:

```sh
scripts/setup/setup-gui-web-2d-vulkan-env.shs --print-install
```

### macOS-Only Checklist

Install or refresh the macOS Vulkan portability stack with Homebrew:

```sh
brew install vulkan-tools vulkan-loader vulkan-headers molten-vk spirv-tools glslang
brew upgrade vulkan-tools vulkan-loader vulkan-headers molten-vk
vulkaninfo --summary
```

The host is Vulkan-ready only when `vulkaninfo --summary` reports the Apple GPU
through MoltenVK, for example `driverName = MoltenVK`. This proves only the
Vulkan loader/ICD path. It does not prove that Chrome or Electron accepted
ANGLE Vulkan, that Simple selected a Vulkan-capable driver, or that RenderDoc
can capture frames.

RenderDoc is a separate prerequisite on macOS. Homebrew may provide the Vulkan
and MoltenVK stack without a RenderDoc package. Record that package state
before claiming the host is capture-ready:

```sh
HOMEBREW_NO_AUTO_UPDATE=1 brew info --cask renderdoc || true
HOMEBREW_NO_AUTO_UPDATE=1 brew info renderdoc || true
```

The setup evidence exposes this as
`gui_web_2d_vulkan_renderdoc_macos_homebrew_package_status` and
`gui_web_2d_vulkan_renderdoc_macos_upstream_support_status`. Upstream official
RenderDoc support currently lists Windows/Linux/Android rather than macOS, so a
macOS completion claim needs a project-approved `RenderDoc.app`/fork or an
unpacked tree that actually contains `renderdoccmd`; a Vulkan-ready MoltenVK
host is not enough. Point the scripts at the concrete bundle/tree:

```sh
export RDOC_HOME=/Applications/RenderDoc.app
scripts/setup/setup-renderdoc-env.shs --check
scripts/setup/setup-renderdoc-env.shs --register-vulkan-layer
```

If `RDOC_HOME` is unset or invalid, the setup scripts now emit stable blocker
keys such as `rdoc_status_reason`,
`gui_web_2d_vulkan_renderdoc_reason`,
`gui_web_2d_vulkan_renderdoc_macos_homebrew_package_status`,
`gui_web_2d_vulkan_renderdoc_macos_upstream_support_status`,
`gui_web_2d_vulkan_renderdoc_search_paths`, and
`gui_web_2d_vulkan_renderdoc_install_hint`. A missing `renderdoccmd` is an
explicit unavailable state, not a skipped pass.

Run the Mac availability probe before any capture claim. The legacy portability
probe remains useful for the macOS report artifact:

```sh
BUILD_DIR=build/renderdoc/macos-portability-current \
REPORT_PATH=build/renderdoc/macos-portability-current/report.md \
sh scripts/check/check-renderdoc-macos-portability-probe.shs
```

On a prepared capture host, opt into real launch/capture attempts:

```sh
RDOC_MACOS_RUN_CAPTURES=1 \
BUILD_DIR=build/renderdoc/macos-portability-capture-current \
REPORT_PATH=build/renderdoc/macos-portability-capture-current/report.md \
sh scripts/check/check-renderdoc-macos-portability-probe.shs
```

The supported macOS RenderDoc debug path is Simple-first:

- Simple 2D/Engine2D Vulkan:
  `scripts/tool/renderdoc-evidence.shs capture-simple`, then
  `scripts/check/check-renderdoc-simple-gate.shs`.

On macOS, Chrome and Electron RenderDoc lanes are exploratory only. They may
render pixels through Metal/OpenGL/SwiftShader while rejecting ANGLE Vulkan, so
they must not be used as completion evidence unless their logs prove Vulkan and
their `.rdc` files pass the same RDOC gates.

For GUI/web/2D comparison work, collect both the browser-hosted surface and the
Simple renderer surface from the same fixture. The browser bitmap lanes are
comparison evidence only until their logs prove Vulkan and their `.rdc` files
pass the RDOC gates:

```sh
SIMPLE_BIN=src/compiler_rust/target/release/simple \
  scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc-simple

SIMPLE_VULKAN_READBACK_WORK_DIR=build/renderdoc/simple-vulkan-readback \
SIMPLE_LIB=src \
  sh scripts/check/check-vulkan-engine2d-readback.shs

sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs
sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

Completion requires typed evidence, not screenshots alone:

- For the supported macOS Simple debug lane, the Simple RenderDoc `.rdc` file
  exists and starts with `RDOC`.
- The Simple lane reports `rdoc_backend=simple`,
  `rdoc_scene=vulkan-engine2d`, and the Simple Vulkan gate passes.
- Any exploratory Electron/Chrome lane reports requested Vulkan/ANGLE metadata and its log
  does not contain Chromium's `angle=vulkan` unavailable failure. A rendered
  bitmap with that log is a browser fallback, not a Vulkan-backed browser proof.
- The production GUI/web parity evidence still reports matching checksums,
  `mismatch_count=0`, and `blur_or_tolerance=false`.

If Chrome or Electron on macOS renders pixels but logs that
`angle=vulkan` is not in the allowed implementations, record
`vulkan-angle-unavailable` in the report and keep the Vulkan browser gate
failed. Current macOS Chromium builds may expose Metal/OpenGL/SwiftShader
without exposing ANGLE Vulkan even when MoltenVK is installed.

Current local macOS result on 2026-06-21:

- `vulkaninfo --summary` reports Apple M4 through `driverName = MoltenVK`.
- `SIMPLE_BIN=src/compiler_rust/target/release/simple
  scripts/setup/setup-gui-web-2d-vulkan-env.shs --run` proves the Simple
  Engine2D Vulkan lane with `gui_web_2d_vulkan_simple_bin_selection_reason=macos-vulkan-loader-paths-present`,
  `gui_web_2d_vulkan_simple_status=pass`,
  `gui_web_2d_vulkan_simple_probe_status=Initialized`, and
  `gui_web_2d_vulkan_simple_backend_name=vulkan`.
- Electron Chromium writes a nonblank ARGB bitmap but records
  `gui_web_2d_vulkan_electron_vulkan_reason=vulkan-angle-unavailable`.
- Chrome writes a screenshot but records
  `gui_web_2d_vulkan_chrome_vulkan_reason=vulkan-angle-unavailable`.
- RenderDoc capture evidence for Simple, Chrome, and Electron records
  `rdoc_capture_status=unavailable` and
  `rdoc_capture_reason=missing-renderdoc` because `renderdoccmd` is not
  installed or discoverable on this host.

### Deferred Windows/Linux Scope

Do not use this top-level guide to claim Windows or Linux GUI/web/2D RenderDoc
completion yet. Add those runbooks later as separate platform sections that
validate the same contract: host Vulkan readiness, Chrome/Electron Vulkan logs,
Simple Engine2D Vulkan readback, and RenderDoc `.rdc` files with `RDOC` magic.
The existing Windows readiness helper can seed that future work, but it is not
currently a passing capture gate.

## Evidence Artifacts

Each capture command writes an `evidence.env` file under its output directory.
Important keys:

- `rdoc_backend`: `simple` or `original`.
- `rdoc_scene`: capture scenario name.
- `rdoc_status_reason`: readiness reason from
  `scripts/setup/setup-renderdoc-env.shs --check`; for macOS missing RenderDoc
  this is usually `missing-renderdoccmd-in-search-paths` or
  `rdoc-home-missing-renderdoccmd`.
- `rdoc_search_paths`: RenderDoc roots checked for `renderdoccmd`.
- `rdoc_install_hint`: platform-specific install or `RDOC_HOME` hint when
  `renderdoccmd` is missing.
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
parity gates. GUI widget witness provenance is inspectable as widget/class
pairs through `gui_widget_rendering_fixture_coverage_spec_widget_classes`,
`gui_widget_rendering_fixture_coverage_render_fixture_widget_classes`, and
`gui_widget_rendering_fixture_coverage_renderdoc_fixture_widget_classes`.
It also re-emits the full W3C CSS inventory count from the SSpec
traceability gate as
`html_css_rendering_manifest_traceability_total_css_property_count` and the
remaining non-rendered inventory count as
`html_css_rendering_manifest_traceability_unrendered_spec_css_property_count`.
The covered render-fixture provenance is inspectable through
`html_css_rendering_manifest_traceability_html_tag_covered` and
`html_css_rendering_manifest_traceability_css_property_covered`, not just the
covered/total counts.
The matching implementation backlog names are emitted as
`html_css_traceability_unsupported_css_properties` and
`html_css_rendering_manifest_traceability_unrendered_spec_css_properties`.
Those unsupported properties are assigned to the inventory SSpec, not claimed as
rendered behavior, until they move into the implemented Simple Web CSS subset.

The nested HTML/CSS RenderDoc goal status gate reports every unsatisfied
RenderDoc goal lane through `renderdoc_goal_blocked_gates` and
`renderdoc_goal_blocked_gate_count`. The top-level GUI audit re-emits those
fields and reports the full completion list through `blocked_completion_gates`
and `blocked_completion_gate_count`, while retaining `blocked_completion_gate`
as the first outstanding gate for older consumers. The top-level list is derived
from the nested Simple/original Chrome RenderDoc lanes, Electron
Chromium/Vulkan RenderDoc gate, and the production GUI/web core parity gate,
so concurrent missing captures are not hidden by a single status reason.

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
  the GUI/web/2D core parity components as `pass`: renderer matrix, 50-case
  layout manifest, live Tauri/Chrome surface manifest, and backend parity. The
  Tauri/Chrome surface manifest must prove live Electron, Tauri, and Chrome
  captures, 50 Tauri and 50 Chrome cases, 36 pass cases plus 14 tracked
  divergence cases for each browser surface, 0 fail cases, 0 mismatch counts,
  `no_fake_capture=true`, and `blur_or_tolerance_used=false`. The GUI RenderDoc
  feature audit records this derived status as
  `production_gui_web_renderer_parity_core_status`. It also re-emits the full
  `scripts/check/check-production-gui-web-renderer-parity-gate.shs` result,
  including font offload/readback and Metal readback fields, but those
  supplemental production lanes do not substitute for or block the narrower
  GUI/web/2D RenderDoc completion claim unless the core parity fields fail.

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

The shared CLI remains the preferred interface. On macOS, run the Simple lane
first and treat Chrome/Electron capture attempts as exploratory until their
Vulkan logs and RDOC gates both pass:

```sh
scripts/setup/setup-renderdoc-env.shs --check
scripts/tool/renderdoc-evidence.shs capture-simple
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
RenderDoc capture and exploratory browser capture attempts through the shared
CLI.
