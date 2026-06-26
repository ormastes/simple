# RenderDoc Capture Infrastructure

Use the shared RenderDoc interface for both capture styles:

```sh
scripts/setup/setup-gui-web-2d-vulkan-env.shs --check
scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
scripts/tool/renderdoc-evidence.shs capture-simple
scripts/tool/renderdoc-evidence.shs capture-html
scripts/tool/renderdoc-evidence.shs capture-electron-html
sh scripts/check/check-html-css-full-rendering-goal-status.shs
RDOC_SIMPLE_EVIDENCE_ENV=build/renderdoc/canonical-probe/simple/evidence.env \
  sh scripts/check/check-renderdoc-simple-gate.shs
RDOC_EXTERNAL_RUN_CAPTURE=1 sh scripts/check/check-renderdoc-external-host-capture.shs
RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/renderdoc/canonical-probe/electron-html/evidence.env \
  sh scripts/check/check-renderdoc-electron-html-gate.shs
PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/production_gui_web_renderer_parity_evidence/evidence.env \
  sh scripts/check/check-production-gui-web-renderer-parity-gate.shs
```

For repeated SSpec coverage of the aggregate audit, set
`GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR` to a build-local cache directory.
The aggregate copies cached nested evidence into each scenario build directory
and keys RenderDoc-dependent gates by their evidence env paths. Leave this unset
for operator evidence refreshes so production reports recompute from current
host state.

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
- `RDOC_SIMPLE_BIN`: optional Simple binary for `capture-simple`. Leave unset
  for normal operator runs so the helper builds
  `src/compiler_rust/target/release/simple`, which carries the current
  `rt_renderdoc_*` extern table.

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

Current platform order is Linux Vulkan first, then macOS Metal/MoltenVK and
Windows D3D12/PIX. Use the Linux render-log gate below before claiming Chrome,
Electron, and Simple are comparable on a Vulkan host.

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
`GUI_WEB_2D_VULKAN_RUN_EVIDENCE_ENV` points at a previous `--run`,
`--renderdoc`, or `--renderdoc-simple` env for full pixel/RenderDoc evidence.
Use `GUI_WEB_2D_VULKAN_BROWSER_BACKING_EVIDENCE_ENV` for focused
`--browser-backing` browser GPU proof. Only `--browser-backing` envs satisfy
`gui_web_2d_vulkan_browser_backing_*`; other modes leave that rollup failed
with `missing-focused-browser-backing`.
If unset, the audit looks for
`build/gui-web-2d-vulkan-env-run-auto/evidence.env` and related run dirs. It
emits `gui_web_2d_vulkan_direct_run_source`,
`gui_web_2d_vulkan_direct_run_evidence_env`, and
`gui_web_2d_vulkan_direct_run_mode` before reporting Electron, Chrome, and
Simple runtime fields. The requested browser Vulkan contract is explicit in
`gui_web_2d_vulkan_electron_requested_api`,
`gui_web_2d_vulkan_electron_requested_angle`,
`gui_web_2d_vulkan_electron_launch_flags`,
`gui_web_2d_vulkan_chrome_requested_api`,
`gui_web_2d_vulkan_chrome_requested_angle`, and
`gui_web_2d_vulkan_chrome_launch_flags`; compare those request keys with the
observed `*_vulkan_status` and `*_vulkan_reason` fields before claiming a
browser lane is Vulkan-backed. The same aggregate evidence exposes the
comparison fixture and viewport through `gui_web_2d_vulkan_html_path`,
`gui_web_2d_vulkan_width`, and `gui_web_2d_vulkan_height`, plus the runtime
artifacts `gui_web_2d_vulkan_electron_argb_path`,
`gui_web_2d_vulkan_chrome_argb_path`, and
`gui_web_2d_vulkan_simple_evidence_env`. The machine-checkable comparison
artifact contract is `gui_web_2d_vulkan_comparison_fixture_status`,
`gui_web_2d_vulkan_comparison_artifact_status`,
`gui_web_2d_vulkan_comparison_artifact_reason`,
`gui_web_2d_vulkan_electron_argb_viewport_match_status`,
`gui_web_2d_vulkan_electron_argb_file_status`,
`gui_web_2d_vulkan_electron_argb_nonblank_status`,
`gui_web_2d_vulkan_chrome_argb_file_status`,
`gui_web_2d_vulkan_chrome_argb_viewport_match_status`,
`gui_web_2d_vulkan_chrome_argb_nonblank_status`,
`gui_web_2d_vulkan_simple_evidence_file_status`, and
`gui_web_2d_vulkan_simple_backend_status`; use those fields to decide whether
the Electron baseline exists and is nonblank, the Chrome ARGB output is
viewport-matching and nonblank, and the Simple evidence env proves the Vulkan backend
before making a GUI/web/2D Vulkan comparison claim.
When direct-run evidence is missing, the aggregate still emits the expected
capture diagnostics under the selected run directory. Inspect
`gui_web_2d_vulkan_electron_stdout`, `gui_web_2d_vulkan_electron_log`,
`gui_web_2d_vulkan_electron_stdout_file_status`,
`gui_web_2d_vulkan_electron_log_file_status`,
`gui_web_2d_vulkan_electron_argb_proof`, and
`gui_web_2d_vulkan_electron_argb_proof_file_status` for Electron capture
failures. Inspect `gui_web_2d_vulkan_chrome_stdout`,
`gui_web_2d_vulkan_chrome_log`,
`gui_web_2d_vulkan_chrome_stdout_file_status`,
`gui_web_2d_vulkan_chrome_log_file_status`,
`gui_web_2d_vulkan_chrome_screenshot`,
`gui_web_2d_vulkan_chrome_argb_stdout`,
`gui_web_2d_vulkan_chrome_argb_stdout_file_status`,
`gui_web_2d_vulkan_chrome_argb_proof`, and
`gui_web_2d_vulkan_chrome_argb_proof_file_status` for Chrome capture
failures. Inspect `gui_web_2d_vulkan_simple_argb_stdout` together with
`gui_web_2d_vulkan_simple_argb_stdout_file_status` and
`gui_web_2d_vulkan_simple_evidence_env` for Simple capture failures. A
`missing` proof, log, stdout, or output file is a completion blocker, not a
substitute for browser or Simple Vulkan proof.
Artifact evidence is not enough for a pixel-equivalence claim. The pairwise
pixel comparison contract is `gui_web_2d_vulkan_pixel_comparison_status`,
`gui_web_2d_vulkan_pixel_comparison_reason`, and
`gui_web_2d_vulkan_pixel_comparison_mode`. It depends on ARGB metadata for all
three surfaces (`gui_web_2d_vulkan_electron_argb_*`,
`gui_web_2d_vulkan_chrome_argb_*`, and
`gui_web_2d_vulkan_simple_argb_*`) plus zero-mismatch diff lanes:
`gui_web_2d_vulkan_electron_chrome_pairwise_diff_status`,
`gui_web_2d_vulkan_electron_chrome_diff_path`,
`gui_web_2d_vulkan_electron_chrome_diff_file_status`,
`gui_web_2d_vulkan_electron_simple_pairwise_diff_status`,
`gui_web_2d_vulkan_electron_simple_diff_path`,
`gui_web_2d_vulkan_electron_simple_diff_file_status`,
`gui_web_2d_vulkan_chrome_simple_pairwise_diff_status`,
`gui_web_2d_vulkan_chrome_simple_diff_path`, and
`gui_web_2d_vulkan_chrome_simple_diff_file_status`. A status of
`pass` requires each zero-mismatch diff artifact file to exist. A status of
`incomplete` with mode `artifact-only-no-pairwise-diff` means the run captured
useful artifacts but did not prove Electron, Chrome, and Simple rendered the
same GUI/web/2D pixels. Missing Electron, Chrome, Simple ARGB input, or diff
artifact files stay in
this incomplete state and is not a mismatch claim. A status of `fail` with mode
`pairwise-argb-diff-mismatch` means the pairwise comparisons ran and found
pixel differences that must be fixed before claiming parity.
Retained showcase performance is also machine-gated. The aggregate consumes
`GUI_SHOWCASE_4K_PERF_ENV` and `GUI_SHOWCASE_8K_PERF_ENV`, forwarding
`gui_showcase_4k_200fps_*` and `gui_showcase_8k_perf_*` rows. Completion
requires the 4K row to prove `3840x2160`, `8294400` pixels, nonzero readback
pixels, target FPS met, nonempty checksum,
`frame_avg_ns`, `frame_p50_ns`, `frame_p95_ns`,
`gui_showcase_4k_200fps_log_file_status=pass`,
`gui_showcase_4k_200fps_time_log_file_status=pass`,
`retained-static-frame`, one redraw frame, at least 200 measured frames, and
`target_fps >= 200`, plus RSS budget status with `max_rss_kb` and
`max_rss_budget_kb`. A pass row must also retain binary provenance:
`source_revision`, `simple_bin`, `use_native=1`,
`native_build_mode=aggressive-native`, and `fallback_state=none`. The default
wrapper budget is 262144 KiB for 4K and
750000 KiB for 8K; rows with `rss_status=measured` are diagnostics, not
completion evidence. The 8K row must likewise prove
`7680x4320`, `33177600` pixels, nonzero readback pixels, target FPS at least
200, positive measured frame count, checksum,
`frame_avg_ns`, `frame_p50_ns`, `frame_p95_ns`,
`gui_showcase_8k_perf_log_file_status=pass`,
`gui_showcase_8k_perf_time_log_file_status=pass`, RSS budget status, and the
same native binary provenance fields. Interpreter or fallback rows remain useful
diagnostics, but they are not 4K/8K completion evidence.
Use `PLAN_ONLY=1 RESOLUTION=4k|8k
scripts/check/check-widget-showcase-4k-200fps.shs` to verify wrapper routing
without launching the expensive native perf run. Plan-only evidence is not
completion evidence; it proves only that the wrapper selects the expected
`*_probe_fn`, `*_probe_prefix`, and `*_perf_env_flag`, and that native alias
generation points at the selected probe. The wrapper emits the full measured
field key shape in plan-only rows with empty FPS, frame timing, observed RSS,
checksum, nonzero readback, render mode, and redraw fields. It also emits
producer-side `*_log_file_status` and `*_time_log_file_status` fields; plan-only
rows should mark them `fail`, while completion rows must mark them `pass`.
When `GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR` is set, the aggregate keys the
HTML/CSS and widget fixture nested caches by the scripts, specs, manifests, and
fixture files that define their evidence. Do not rely on old unkeyed cache
directories; they are intentionally ignored so stale `105/105` or blocked
animation rows cannot survive after the implemented CSS subset changes.
The browser Vulkan-backed proof is a separate rollup:
`gui_web_2d_vulkan_browser_backing_status`,
`gui_web_2d_vulkan_browser_backing_reason`, and
`gui_web_2d_vulkan_browser_backing_mode`. Missing focused proof reports
`focused-browser-backing-required` and emits Electron/Chrome child backing
statuses as `unavailable` with `missing-focused-browser-backing`, not blank.
Pixel comparison artifacts are useful
comparison evidence, but they are not Electron/Chrome Vulkan-backed proof. The
focused `--browser-backing` probe can provide `gpu-feature-status` evidence.
The aggregate rejects a summary-only browser backing pass: Electron must report
`gui_web_2d_vulkan_electron_browser_backing_status=pass`,
`gui_web_2d_vulkan_electron_browser_backing_reason=electron-vulkan-backed`,
an `enabled` Vulkan feature value, and
`gui_web_2d_vulkan_electron_browser_backing_hardware_supports_vulkan=true`;
Chrome must report `gui_web_2d_vulkan_chrome_browser_backing_status=pass`,
`gui_web_2d_vulkan_chrome_browser_backing_reason=chrome-vulkan-backed`,
`gui_web_2d_vulkan_chrome_browser_backing_hardware_supports_vulkan=true`, and
Vulkan in either display type or GL implementation parts.
The `--browser-backing` setup producer uses the same rule; Chrome hardware
missing with Vulkan-looking display/GL text is emitted as
`chrome-vulkan-hardware-missing`, not a pass.
Both Electron and Chrome child passes also require their
`*_browser_backing_source` files to exist and `gpu_compositing` to remain
enabled in the captured GPU feature status; the `--browser-backing` producer
emits `*_browser_backing_source_file_status`, and the aggregate verifies or
recomputes that status for older evidence before accepting proof.
Electron browser backing uses the compact `electron_argb_proof.json` as its
`gui_web_2d_vulkan_electron_browser_backing_source`; the full ARGB capture is
reported separately as `gui_web_2d_vulkan_electron_browser_backing_argb_source`
so operators do not need to open the large pixel payload to inspect GPU state.
When `ELECTRON_CAPTURE_REMOTE_DEBUGGING_PORT` is set, the Electron capture tool
also records browser-target CDP `SystemInfo.getInfo` status in
`gui_web_2d_vulkan_electron_browser_backing_browser_target_gpu_info_status` and
`..._reason`; a reachable browser target is diagnostic only and still must
produce Vulkan renderer fields before Electron can pass browser backing.
The aggregate also normalizes stale child rows: a child `pass` without those
matching proof fields is emitted as `fail` with `electron-vulkan-proof-missing`
or `chrome-vulkan-proof-missing`, so agents must fix the probe evidence rather
than copying a prior pass row.
For failed or partial hosts, inspect
`gui_web_2d_vulkan_electron_browser_backing_vulkan`,
`gui_web_2d_vulkan_electron_browser_backing_gpu_compositing`,
`gui_web_2d_vulkan_electron_browser_backing_display_type`,
`gui_web_2d_vulkan_electron_browser_backing_hardware_supports_vulkan`,
`gui_web_2d_vulkan_electron_browser_backing_gl_implementation_parts`,
`gui_web_2d_vulkan_electron_browser_backing_skia_backend_type`,
`gui_web_2d_vulkan_electron_browser_backing_gl_renderer`,
`gui_web_2d_vulkan_chrome_browser_backing_display_type`,
`gui_web_2d_vulkan_chrome_browser_backing_gpu_compositing`,
`gui_web_2d_vulkan_chrome_browser_backing_gl_implementation_parts`,
`gui_web_2d_vulkan_chrome_browser_backing_skia_backend_type`,
`gui_web_2d_vulkan_chrome_browser_backing_gl_renderer`, and the
matching `*_browser_backing_source` files before changing Chromium flags.
RenderDoc capture and gate readiness remains a separate blocker reported by
`gui_web_2d_vulkan_renderdoc_blocker_*`.
As of 2026-06-26, Linux evidence has Chrome Vulkan-backed and Simple Vulkan
passing with pairwise pixel parity. Electron direct Vulkan status can report
`enabled_on`, but focused browser backing still fails unless Electron also
proves a Vulkan renderer path through `hardwareSupportsVulkan=true` and Vulkan
in display type, GL implementation parts, Skia backend, or GL renderer. Current
Linux evidence reports `electron-vulkan-enabled-without-angle-vulkan-proof`
with `(gl=none,angle=none)` and `skia=None`; do not treat that as a browser
Vulkan pass. The current status and rejected shortcuts are tracked in
`doc/08_tracking/bug/gui_web_2d_vulkan_browser_backing_2026-06-23.md`.
The current blockers are machine-readable in
`gui_web_2d_vulkan_renderdoc_blocker_status`,
`gui_web_2d_vulkan_renderdoc_blocker_reason`,
`gui_web_2d_vulkan_renderdoc_blocker_gate_count`, and
`gui_web_2d_vulkan_renderdoc_blocker_gates`. These fields distinguish host
Vulkan readiness, RenderDoc command availability, Simple RenderDoc gate status,
Electron ANGLE Vulkan acceptance, Electron RenderDoc gate status, Chrome ANGLE
Vulkan acceptance, Chrome RenderDoc gate status, and pairwise pixel comparison.
A blocker status of `blocked` means the GUI/web/2D comparison can still be
useful, but at least one required Vulkan-backed `.rdc` proof or pixel-diff lane
remains a completion blocker.

As of 2026-06-25 on Linux x86_64, the prepared host state is:
Chrome `139.0.7258.138`, repo-local Electron `30.5.1`, RenderDoc
`/usr/local/bin/renderdoccmd` v1.44, Vulkan hardware selection
`Intel(R) Graphics (RPL-P)`, `glslangValidator`, `spirv-as`, and a Rustup
stable toolchain (`rustc`/`cargo` 1.96). `--check` reports RenderDoc ready from
`PATH:renderdoccmd`; `--run` reports Simple Vulkan readback pass and
Electron/Chrome/Simple pairwise ARGB pixel parity. `--browser-backing` still
fails because Electron reports `electron-vulkan-enabled-without-angle-vulkan-proof`
with no ANGLE/Skia Vulkan renderer proof, while Chrome reports ANGLE Vulkan
hardware support. `--renderdoc-simple` now builds the
Rust interpreter and resolves `rt_renderdoc_*`; the remaining blocker is that
RenderDoc returns `renderdoc_end=0`, `renderdoc_num_captures=0`, and no `.rdc`
for the headless Simple Engine2D frame.

Linux setup commands used for this state:

```sh
sudo apt-get install -y glslang-tools spirv-tools rustup
rustup toolchain install stable --profile minimal
rustup default stable
(cd tools/electron-shell && npm install)
(cd src/compiler_rust && cargo build --release --bin simple)
```

Ubuntu's packaged Cargo 1.75 cannot parse this repo's lockfile version 4; use
Rustup stable for the RenderDoc Simple interpreter build.

### Linux Vulkan Render-Log Compare

The Linux-first comparison gate normalizes existing aggregate evidence and
optional native RenderDoc evidence into the Simple render-log format:

```sh
GUI_WEB_2D_VULKAN_ENV=build/gui-web-2d-vulkan-env/evidence.env \
GUI_WEB_2D_VULKAN_BROWSER_BACKING_EVIDENCE_ENV=build/gui-web-2d-vulkan-env-browser-backing/evidence.env \
sh scripts/check/check-linux-vulkan-render-log-compare.shs
```

By default this Linux row consumes the focused RenderDoc evidence paths:

- `build/gui-web-2d-vulkan-env-renderdoc-simple/renderdoc/simple/evidence.env`
- `build/renderdoc/chrome-display-helper/evidence.env`
- `build/renderdoc/electron-display-helper/electron-html/evidence.env`

Override `RDOC_SIMPLE_EVIDENCE_ENV`, `RDOC_HTML_EVIDENCE_ENV`, or
`RDOC_ELECTRON_HTML_EVIDENCE_ENV` only when deliberately comparing a different
capture set.

It writes:

- `build/linux-vulkan-render-log-compare/evidence.env`
- `build/linux-vulkan-render-log-compare/simple.srl.env`
- `build/linux-vulkan-render-log-compare/chrome.srl.env`
- `build/linux-vulkan-render-log-compare/electron.srl.env`
- `build/linux-vulkan-render-log-compare/compare.srl.env`

The gate is fail-closed. It reads direct-run pixel comparison from
`GUI_WEB_2D_VULKAN_ENV` and focused Chrome/Electron GPU-status proof from
`GUI_WEB_2D_VULKAN_BROWSER_BACKING_EVIDENCE_ENV` when present. If
`GUI_WEB_2D_VULKAN_ENV` is itself a fresh `--browser-backing` run, that main env
wins over a stale separate focused env; otherwise the separate focused env is
used and older combined fixtures fall back to `GUI_WEB_2D_VULKAN_ENV`. It
requires Simple Vulkan backend evidence, focused Chrome and Electron Vulkan
browser backing, `pairwise-argb-diff` mode, and all three pairwise diff lanes to
pass. Missing RenderDoc `.rdc` evidence is reported through
`linux_vulkan_render_log_compare_renderdoc_*_status` plus the matching
`linux_vulkan_render_log_compare_renderdoc_*_reason`; by default Simple,
Chrome, and Electron RenderDoc rows must pass with real `.rdc` files and `RDOC`
magic. Set `LINUX_VULKAN_RENDER_LOG_REQUIRE_RDOC=0` only for diagnostic
partial-log inspection, and never use that mode to claim Linux platform-matrix
completion.

Current Linux host evidence on 2026-06-25 has
`linux_vulkan_render_log_compare_pairwise_status=pass`, Simple RenderDoc
`pass`, Chrome RenderDoc `fail`, and Electron RenderDoc `fail`. Current focused
browser backing passes, but the row remains failed because the required Chrome
and Electron native RenderDoc lanes are still not pass; do not treat passing
pairwise ARGB or browser-GPU proof as RenderDoc completion.

Completion keys:

```text
linux_vulkan_render_log_compare_status=pass
linux_vulkan_render_log_compare_required_api=vulkan
linux_vulkan_render_log_compare_pairwise_status=pass
linux_vulkan_render_log_compare_renderdoc_simple_status=pass
linux_vulkan_render_log_compare_renderdoc_simple_reason=pass
linux_vulkan_render_log_compare_renderdoc_chrome_status=pass
linux_vulkan_render_log_compare_renderdoc_chrome_reason=pass
linux_vulkan_render_log_compare_renderdoc_electron_status=pass
linux_vulkan_render_log_compare_renderdoc_electron_reason=pass
```

The source logs use `simple-render-log-v1` and include
`simple_render_log_reason` for normalized failure detail and
`simple_render_log_native_info` for native-only metadata that does not yet fit
the normalized schema. Metal, D3D12/PIX, GPU debugger, and Tauri mobile lanes
must keep this schema and add native sidecar fields instead of inventing
unrelated key names. If any required render-log or native capture field is
missing, completion remains `incomplete`.

### macOS Metal Render-Log Compare

The macOS gate normalizes native Metal generated/readback evidence, Engine2D
framebuffer readback evidence, and Chrome/Electron Metal-backed browser
evidence:

```sh
METAL_GENERATED_2D_READBACK_ENV=build/metal_generated_2d_readback/evidence.env \
METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV=build/metal_engine2d_framebuffer_readback_evidence/evidence.env \
MACOS_METAL_BROWSER_ENV=build/macos-metal-browser-backing/evidence.env \
sh scripts/check/check-macos-metal-render-log-compare.shs
```

Set `MACOS_METAL_RENDER_LOG_REQUIRE_GPU_CAPTURE=1` on a host where Xcode GPU
Frame Capture evidence is expected. Completion keys:

```text
macos_metal_render_log_compare_status=pass
macos_metal_render_log_compare_required_api=metal
macos_metal_render_log_compare_pairwise_status=pass
macos_metal_render_log_compare_gpu_capture_status=pass
```

The gate rejects missing Metal submit/readback, missing raw framebuffer
download, checksum mismatch, browser fallback, and non-pairwise comparisons.

### Windows D3D12/PIX Render-Log Compare

The Windows gate requires explicit D3D12 native readback evidence and
Chrome/Electron D3D12-backed browser evidence. The older DirectX/D3D11 wrapper
is diagnostic only unless its evidence explicitly states `d3d12`.

```sh
WINDOWS_D3D12_NATIVE_READBACK_ENV=build/windows-d3d12-native-readback/evidence.env \
WINDOWS_D3D12_BROWSER_ENV=build/windows-d3d12-browser-backing/evidence.env \
WINDOWS_D3D12_PIX_ENV=build/windows-d3d12-pix/evidence.env \
sh scripts/check/check-windows-d3d12-render-log-compare.shs
```

Set `WINDOWS_D3D12_RENDER_LOG_REQUIRE_PIX=1` when PIX or an equivalent GPU
debugger capture is required. Completion keys:

```text
windows_d3d12_render_log_compare_status=pass
windows_d3d12_render_log_compare_required_api=d3d12
windows_d3d12_render_log_compare_pairwise_status=pass
windows_d3d12_render_log_compare_pix_status=pass
windows_d3d12_render_log_compare_gpu_debugger_status=pass
```

The gate rejects D3D11-only evidence, missing PIX/GPU-debugger proof in strict
mode, browser fallback, and non-pairwise comparisons.

The GUI RenderDoc aggregate consumes these normalized render-log compare
outputs without launching them:

```sh
LINUX_VULKAN_RENDER_LOG_COMPARE_ENV=build/linux-vulkan-render-log-compare/evidence.env
MACOS_METAL_RENDER_LOG_COMPARE_ENV=build/macos-metal-render-log-compare/evidence.env
WINDOWS_D3D12_RENDER_LOG_COMPARE_ENV=build/windows-d3d12-render-log-compare/evidence.env
```

Completion keys are:

```text
native_render_log_platform_matrix_status=pass
native_render_log_platform_matrix_required_platforms=linux-vulkan,macos-metal,windows-d3d12
native_render_log_platform_matrix_missing_platforms=
```

The aggregate revalidates each platform row before marking the matrix complete:
Linux must report `required_api=vulkan`, `pairwise_status=pass`, and pass
RenderDoc statuses for Simple, Chrome, and Electron; macOS must report
`required_api=metal`, `pairwise_status=pass`, and GPU capture status `pass`;
Windows must report `required_api=d3d12`, `pairwise_status=pass`, PIX status
`pass`, and GPU debugger status `pass`. A stale or forged
`*_render_log_compare_status=pass` without those fields is downgraded to a
failed platform row.

If any platform compare evidence is missing or failing, the aggregate keeps
`gui_renderdoc_feature_coverage_status` incomplete and adds the native
render-log platform matrix to `blocked_completion_gates`.

On Linux and macOS, the wrapper prefers `src/compiler_rust/target/release/simple`
or `src/compiler_rust/target/debug/simple` when that binary is the required
fresh driver for the active lane. The selected executable is recorded
as `gui_web_2d_vulkan_simple_bin`, with the reason in
`gui_web_2d_vulkan_simple_bin_selection_reason`. If `bin/simple` is missing in
a linked worktree, the wrapper falls back to compiler-rust release/debug, then a
PATH `simple` only when the resolved executable belongs to the same Git
repository, then checked-in wrappers. It records
`default-missing-same-repo-path-fallback` for the guarded PATH case and
`default-missing-fallback` for local file fallbacks. If no fresh driver exists and `bin/simple` is older
than the Rust runtime changes under test, build the driver and rerun:

```sh
(cd src/compiler_rust && cargo build --release --bin simple)
scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
```

On a prepared RenderDoc host, debug the Simple in-application RenderDoc lane
first:

```sh
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
scripts/setup/setup-gui-web-2d-vulkan-env.shs --check
```

If `RDOC_HOME` is unset or invalid, the setup scripts now emit stable blocker
keys such as `gui_web_2d_vulkan_renderdoc_reason`,
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
pass the RDOC gates. The `--run` helper writes Electron, Chrome, and Simple
ARGB captures plus three pairwise diff lanes into the
`gui_web_2d_vulkan_*` evidence namespace:

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
- The aggregate audit reports `gui_web_2d_vulkan_comparison_artifact_status=pass`
  or records an explicit `gui_web_2d_vulkan_comparison_artifact_reason` for the
  missing or mismatched comparison artifact.
- The aggregate audit reports `gui_web_2d_vulkan_pixel_comparison_status=pass`
  with `gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff`, proving
  Electron, Chrome, and Simple ARGB outputs were pairwise compared with zero
  mismatches. Missing ARGB input reports `incomplete` with
  `artifact-only-no-pairwise-diff`. If it reports `fail` with
  `pairwise-argb-diff-mismatch`, the comparison ran and exposed real pixel
  differences; do not downgrade that to missing evidence.
- The aggregate audit reports `gui_web_2d_vulkan_browser_backing_status=pass`
  and `gui_web_2d_vulkan_renderdoc_blocker_status=pass`; otherwise these fields
  are completion blockers, not warnings.
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

### Cross-Platform Scope

Do not use one platform gate to claim another platform. Linux Vulkan, macOS
Metal, and Windows D3D12/PIX must each pass their own `simple-render-log-v1`
comparison gate on a matching native host.

## Evidence Artifacts

Each capture command writes an `evidence.env` file under its output directory.
Important keys:

- `rdoc_backend`: `simple` or `original`.
- `rdoc_scene`: capture scenario name.
- `gui_web_2d_vulkan_renderdoc_reason`: readiness reason from
  `scripts/setup/setup-gui-web-2d-vulkan-env.shs --check`; for macOS missing
  RenderDoc this is usually `missing-renderdoccmd-in-search-paths` or
  `rdoc-home-missing-renderdoccmd`.
- `gui_web_2d_vulkan_renderdoc_search_paths`: RenderDoc roots checked for
  `renderdoccmd`.
- `gui_web_2d_vulkan_renderdoc_install_hint`: platform-specific install or
  `RDOC_HOME` hint when `renderdoccmd` is missing.
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
the 105/105 HTML tag coverage and 129/129 implemented CSS property coverage in
the same evidence env as the Simple, original Chrome, Electron, and production
parity gates. GUI widget witness provenance is inspectable as widget/class
pairs through `gui_widget_rendering_fixture_coverage_spec_widget_classes`,
`gui_widget_rendering_fixture_coverage_render_fixture_widget_classes`, and
`gui_widget_rendering_fixture_coverage_renderdoc_fixture_widget_classes`.
The RenderDoc fixture also carries one semantic `data-render-feature` witness
per widget; the audit exposes these as
`gui_widget_rendering_fixture_coverage_renderdoc_fixture_widget_features`,
checks them against
`gui_widget_rendering_fixture_coverage_expected_renderdoc_fixture_features`,
and fails closed through
`gui_widget_rendering_fixture_coverage_missing_renderdoc_fixture_features`.
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
The implemented `transform` subset is intentionally limited to static
`translate(...)`, `translateX(...)`, and `translateY(...)` pixel offsets; it is
covered by renderer pixel tests, while the live manifest carries a no-op
fixture witness to keep existing Chrome/Electron bitmap baselines stable.
The focused full-rendering status gate
`scripts/check/check-html-css-full-rendering-goal-status.shs` makes that split
explicit: `html_css_full_rendering_goal_html_tag_status=pass` and
`html_css_full_rendering_goal_implemented_css_status=pass` are required before
the broader goal can progress, while
`html_css_full_rendering_goal_full_css_status=incomplete` remains the honest
state until every W3C CSS inventory property has rendered fixture coverage.
Animation-related CSS is also reported as its own sub-goal:
`html_css_full_rendering_goal_animation_css_status`,
`html_css_full_rendering_goal_animation_css_total_count`,
`html_css_full_rendering_goal_animation_css_rendered_count`, and
`html_css_full_rendering_goal_animation_css_unrendered_properties` cover the
`animation-*`, `transition-*`, and `transform-*` families. The top-level GUI
RenderDoc audit only keeps `CSS animation/transition/transform rendering coverage`
in `blocked_completion_gates` when that sub-goal is incomplete; do not use a
generic CSS inventory count as animation proof without the fixture evidence.
Use `--strict` when a CI or release lane should fail unless the full CSS
inventory is rendered.

The nested HTML/CSS RenderDoc goal status gate reports every unsatisfied
RenderDoc goal lane through `renderdoc_goal_blocked_gates` and
`renderdoc_goal_blocked_gate_count`. The top-level GUI audit re-emits those
fields and reports the full completion list through `blocked_completion_gates`
and `blocked_completion_gate_count`, while retaining `blocked_completion_gate`
as the first outstanding gate for older consumers. The top-level list is derived
from the nested Simple/original Chrome RenderDoc lanes, Electron
Chromium/Vulkan RenderDoc gate, modern Web WM Electron visual/interaction
evidence, and the production GUI/web core parity gate, so concurrent missing
captures are not hidden by a single status reason.
Callers that already produced fresh HTML/CSS traceability evidence may set
`HTML_CSS_TRACEABILITY_EVIDENCE_ENV`; callers that already produced fresh
rendering-manifest traceability evidence may set
`HTML_CSS_RENDERING_MANIFEST_TRACEABILITY_ENV`. The nested gate reuses those
files instead of rerunning the heavy checkers. A configured but missing file is
a fail-closed state, not permission to fall back to stale build artifacts.

For the HTML-backed GUI modernization claim, the top-level audit consumes
`scripts/check/check-web-wm-modern-shell-evidence.shs` through
`web_wm_modern_shell_evidence_*` keys. Completion requires
`web_wm_modern_shell_evidence_status=pass`,
`web_wm_modern_shell_evidence_bitmap_nonblank_status=pass`,
`web_wm_modern_shell_evidence_audit_pass=pass`, and
`web_wm_modern_shell_evidence_interaction_pass=pass` with focus, keyboard,
input, pointer, and click evidence. `environment-unavailable` remains a useful
host diagnosis but is still reported as `modern Web WM Electron visual and
interaction evidence` in `blocked_completion_gates` until a real Electron host
produces the pass row.

For the all-GUI-item claim, use the focused wrapper
`scripts/check/check-gui-widget-renderdoc-goal-status.shs`. It composes the
43/43 widget fixture feature witness gate with the Simple Vulkan Engine2D
RenderDoc gate and the Electron Chromium/Vulkan HTML gate. Normal runs may
return `gui_widget_renderdoc_goal_status=incomplete` on hosts without live
macOS RenderDoc evidence; release/completion lanes should pass `--strict` and
require `gui_widget_renderdoc_goal_widget_feature_covered_count=43`,
`gui_widget_renderdoc_goal_simple_gate_status=pass`,
`gui_widget_renderdoc_goal_simple_gate_source_env_file_status=pass`,
`gui_widget_renderdoc_goal_simple_gate_capture_file_status=pass`,
`gui_widget_renderdoc_goal_electron_gate_status=pass`, and
`gui_widget_renderdoc_goal_electron_gate_reason=pass`,
`gui_widget_renderdoc_goal_electron_gate_failure_class=pass`,
`gui_widget_renderdoc_goal_electron_gate_source_env_file_status=pass`,
`gui_widget_renderdoc_goal_electron_gate_capture_file_status=pass`,
`gui_widget_renderdoc_goal_electron_gate_argb_file_status=pass`, and
`gui_widget_renderdoc_goal_blocked_gate_count=0`.
The top-level GUI audit now runs that focused wrapper, re-emits
`gui_widget_renderdoc_goal_status`, `gui_widget_renderdoc_goal_reason`,
`gui_widget_renderdoc_goal_blocker_doc`,
`gui_widget_renderdoc_goal_simple_blocker_doc`,
`gui_widget_renderdoc_goal_electron_blocker_doc`,
`gui_widget_renderdoc_goal_simple_gate_status`,
`gui_widget_renderdoc_goal_simple_gate_source_env_file_status`,
`gui_widget_renderdoc_goal_simple_gate_capture_file_status`,
`gui_widget_renderdoc_goal_electron_gate_status`, and
`gui_widget_renderdoc_goal_electron_gate_reason`,
`gui_widget_renderdoc_goal_electron_gate_failure_class`,
`gui_widget_renderdoc_goal_electron_gate_source_env_file_status`,
`gui_widget_renderdoc_goal_electron_gate_capture_file_status`,
`gui_widget_renderdoc_goal_electron_gate_argb_file_status`, and
`gui_widget_renderdoc_goal_blocked_gate_count`, and remains incomplete until
the widget goal reaches `pass`. Any focused widget blocker reported by the
widget goal is also included in top-level `blocked_completion_gates` so the
top-level reason is not disconnected from the full completion list. Use
`doc/08_tracking/bug/gui_widget_renderdoc_goal_blockers_2026-06-23.md` for the
current Simple/Electron widget RenderDoc blocker record.

The current canonical evidence contract is:

- Simple in-application path:
  `build/renderdoc/canonical-probe/simple/evidence.env` must report
  `rdoc_backend=simple`, `rdoc_scene=vulkan-engine2d`,
  `rdoc_program=src/app/test/renderdoc_vulkan_capture.spl`,
  `rdoc_capture_status=pass`, `rdoc_capture_magic=RDOC`, and an existing
  `.rdc` file. It must also carry the probe log-derived runtime metadata:
  `rdoc_simple_runtime_backend=vulkan`, `rdoc_simple_renderdoc_available=1`,
  `rdoc_simple_renderdoc_start=1`, a recorded `rdoc_simple_renderdoc_end`, a
  positive `rdoc_simple_renderdoc_num_captures`, and a positive
  `rdoc_simple_pixel_count`. The Simple gate emits
  `rdoc_simple_gate_runtime_metadata_status` and
  `rdoc_simple_gate_missing_runtime_metadata` so a partial `.rdc` capture cannot
  look like a Vulkan-backed pass. The aggregate RenderDoc goal requires this through
  `scripts/check/check-renderdoc-simple-gate.shs`; if that env/file is missing
  or not the Simple Vulkan Engine2D probe path, the GUI RenderDoc goal remains
  incomplete. The top-level GUI RenderDoc feature audit re-emits the Simple
  evidence env, capture status/magic/file, gate status/reason, runtime metadata
  status/missing list, and required backend/scene/program/status/magic fields so
  the Simple Vulkan requirement is visible without opening the nested goal report.
  Current Linux evidence from 2026-06-25 has this Simple gate passing with
  `rdoc_simple_runtime_backend=vulkan` and an `RDOC` capture. The remaining
  widget RenderDoc blocker is Electron: the canonical Electron helper uses
  `xvfb-run -a --server-args="-screen 0 ${width}x${height}x24"` on headless
  Linux, requests `--enable-features=Vulkan --use-angle=vulkan`, and currently
  records `chromium-gpu-process-crashed-under-renderdoc` before ARGB or `.rdc`
  output is produced. Local 2026-06-25 probes also rejected
  `--in-process-gpu`, `--single-process`, GL/ANGLE fallback, and removing
  `--opt-hook-children`; none produced both nonblank ARGB and an `RDOC`
  capture.
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
  parity gate emits `production_gui_web_renderer_parity_gate_source_env` and
  `production_gui_web_renderer_parity_gate_source_env_status` so a missing
  source env is tied to the exact checked file and typed as `missing` instead
  of only a reason string. A source env that exists but omits the top-level
  `production_gui_web_renderer_parity_status` is partial evidence and must
  report `partial-production-parity-source-status`,
  `production_gui_web_renderer_parity_gate_source_partial_status=partial`, and
  `production_gui_web_renderer_parity_gate_refresh_command`; matrix-only
  evidence is not live renderer parity evidence.
  wrapper exports the resolved `SIMPLE_BIN` to nested parity checks and records
  `production_gui_web_renderer_parity_simple_bin` plus
  `production_gui_web_renderer_parity_simple_bin_source`; a clean worktree with
  no `src/compiler_rust/target/release/simple` should use repo/path fallback
  evidence instead of failing with `missing-simple-bin`. Font offload
  `unavailable` is recorded but does not satisfy the production parity wrapper.
  The Tauri/Chrome surface manifest must prove live Electron, Tauri, and Chrome
  captures, 50 Tauri and 50 Chrome cases, 36 pass cases plus 14 tracked
  divergence cases for each browser surface, 0 fail cases, 0 mismatch counts,
  `no_fake_capture=true`, and `blur_or_tolerance_used=false`. The GUI RenderDoc
  feature audit records this derived status as
  `production_gui_web_renderer_parity_core_status`. It also re-emits the full
  `scripts/check/check-production-gui-web-renderer-parity-gate.shs` result,
  including font offload/readback and Metal readback fields, but those
  supplemental production lanes do not substitute for or block the narrower
  GUI/web/2D RenderDoc completion claim unless the core parity fields fail.
  Passing surface capture rows must also carry explicit capture provenance:
  `production_gui_web_renderer_parity_surface_manifest_tauri_capture_backend`,
  `production_gui_web_renderer_parity_surface_manifest_tauri_capture_required_commands`,
  empty
  `production_gui_web_renderer_parity_surface_manifest_tauri_capture_missing_commands`,
  and
  `production_gui_web_renderer_parity_surface_manifest_chrome_capture_backend`.
  Missing provenance or nonempty missing-command evidence fails the gate instead
  of being backfilled from the current host.

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

The top-level GUI RenderDoc aggregate consumes the focused Chrome wrapper
summary from `build/renderdoc/chrome-display-helper/evidence.env` by default.
That summary is produced with:

```sh
RDOC_EXTERNAL_RUN_CAPTURE=1 \
  BUILD_DIR=build/renderdoc/chrome-display-helper \
  sh scripts/check/check-renderdoc-external-host-capture.shs
```

If Chrome's GPU process crashes while hooked by RenderDoc before any `.rdc` is
written, the capture remains failed but the raw reason is preserved as
`rdoc_external_host_capture_reason_raw=chromium-gpu-process-crashed-under-renderdoc`
instead of the generic `missing-rdc`.

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

Linux note, 2026-06-26: the Simple in-application capture must pass RenderDoc's
Vulkan device pointer, not `VkDevice`. RenderDoc documents the Vulkan pointer as
the dispatch table pointer stored at the start of `VkInstance`; the Rust
interpreter exposes this through `rt_vulkan_get_renderdoc_device_pointer`.
Loose RenderDoc installs may also ship `renderdoccmd` as a symlink and an
unregistered Vulkan layer manifest with a stale `library_path`. The helper
resolves the real RenderDoc home, creates a per-run layer manifest pointing at
`librenderdoc.so`, and forces `VK_LAYER_RENDERDOC_Capture` with
`VK_INSTANCE_LAYERS`. Current focused evidence is produced by
`GUI_WEB_2D_VULKAN_BUILD_DIR=build/gui-web-2d-vulkan-env-renderdoc-simple
scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc-simple`, and the
aggregate defaults `RDOC_SIMPLE_EVIDENCE_ENV` to
`build/gui-web-2d-vulkan-env-renderdoc-simple/renderdoc/simple/evidence.env`.
That evidence passes with `rdoc_simple_renderdoc_capturing_after_start=1`,
`rdoc_simple_renderdoc_end=1`, `rdoc_simple_renderdoc_num_captures=1`,
`rdoc_capture_status=pass`, and `rdoc_capture_magic=RDOC`.

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

## Linux Browser Backing Notes

On Linux, the Chromium/Electron browser-backing check is separate from the
browser RenderDoc `.rdc` gate. Electron 42 requires X11 ozone for the Vulkan
path; Wayland reports that it is not compatible with Vulkan. The canonical
Electron capture flags are:

```sh
--no-sandbox --disable-gpu-sandbox --disable-dev-shm-usage \
  --ozone-platform=x11 --enable-features=Vulkan --use-angle=vulkan
```

The Electron HTML capture helper samples `app.getGPUFeatureStatus()` after
`BrowserWindow.capturePage()`, so the recorded status reflects the active
rendering path instead of the early startup default. Current Linux evidence
passes the browser-backing gate with
`gui_web_2d_vulkan_browser_backing_status=pass` and
`gui_web_2d_vulkan_electron_browser_backing_vulkan=enabled_on` but no
Electron ANGLE/Vulkan backing proof in:

```sh
build/gui-web-2d-vulkan-env-browser-backing-electron42/evidence.env
```

RenderDoc browser `.rdc` capture is still tracked separately. On Linux the
helper now prefers an existing real `DISPLAY` and records
`rdoc_chrome_display_mode` / `rdoc_electron_display_mode` in evidence. Xvfb is
kept as fallback or can be forced with `RDOC_CHROME_USE_XVFB=1` and
`RDOC_ELECTRON_USE_XVFB=1`, but Xvfb is not a strong Vulkan-present proof on
this host because Chrome reports missing DRI3 support when child-process
hooking is disabled.

Current real-display evidence still does not satisfy the browser `.rdc` gates:
Chrome with RenderDoc child-process hooking exits the Chromium GPU process with
code 139 and is recorded as
`chromium-gpu-process-crashed-under-renderdoc`; Chrome single-process reports
that Vulkan is unsupported in the in-process GPU path; and Electron
42/X11/Vulkan captures ARGB outside RenderDoc but exits with `SIGTRAP` under
`renderdoccmd capture` before ARGB or `.rdc` output, recorded as
`electron-process-sigtrap-under-renderdoc`.

For GPU-process-only diagnostics, use:

```sh
RDOC_CHROME_GPU_LAUNCHER=1 \
  RDOC_OUTPUT_DIR=build/renderdoc/chrome-gpu-launcher-helper \
  scripts/tool/renderdoc-evidence.shs capture-html

RDOC_ELECTRON_GPU_LAUNCHER=1 \
  RDOC_OUTPUT_DIR=build/renderdoc/electron-gpu-launcher-helper \
  scripts/tool/renderdoc-evidence.shs capture-electron-html
```

These modes pass Chromium's `--gpu-launcher` to
`scripts/tool/renderdoc-gpu-launcher.shs`, so RenderDoc wraps only the GPU
process instead of recursively hooking every child process. On the current
Linux host this still does not satisfy the `.rdc` gates: Chrome repeatedly
restarts the GPU process with no capture, and Electron fails with
`UnknownVizError` before ARGB or `.rdc` output.

The launcher also has an in-process autocapture variant:

```sh
RDOC_CHROME_GPU_AUTOCAPTURE=1 \
  RDOC_OUTPUT_DIR=build/renderdoc/chrome-gpu-autocapture-wrap \
  scripts/tool/renderdoc-evidence.shs capture-html

RDOC_ELECTRON_GPU_AUTOCAPTURE=1 \
  RDOC_OUTPUT_DIR=build/renderdoc/electron-gpu-autocapture-wrap \
  scripts/tool/renderdoc-evidence.shs capture-electron-html
```

Autocapture builds and preloads
`scripts/tool/renderdoc-vulkan-autocapture.c`, which wraps
`dlsym`, `vkGetDeviceProcAddr`, `vkGetInstanceProcAddr`, `vkQueueSubmit`,
`vkQueueSubmit2`, `vkQueueSubmit2KHR`, and `vkQueuePresentKHR` to call
RenderDoc's in-application capture API from inside the GPU process. Current
Linux evidence records `rdoc_autocapture_loaded=1` and confirms Chromium asks
`dlsym` for `vkGetInstanceProcAddr`, but it does not reach the wrapped queue
hooks before timeout/failure, so this remains diagnostic evidence rather than a
passing `.rdc` gate. `RDOC_GPU_LAUNCHER_START_ON_DLSYM=1` is an opt-in
diagnostic that starts capture as soon as `vkGetInstanceProcAddr` is resolved;
on this host it crashes Chrome's GPU process with exit code 139 and still does
not produce `.rdc`, so keep it off for canonical evidence runs.

For the Simple-side GUI widget RenderDoc proof, capture the generated widget
fixture with the dedicated Simple program:

```sh
RDOC_OUTPUT_DIR=build/renderdoc/widget-probe-small \
RDOC_SIMPLE_PROG="$PWD/src/app/test/renderdoc_vulkan_widget_capture.spl" \
RDOC_HTML_PATH="$PWD/test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html" \
  scripts/tool/renderdoc-evidence.shs capture-simple
```

The corresponding gate is:

```sh
sh scripts/check/check-gui-widget-renderdoc-goal-status.shs
```

Passing Simple widget evidence records
`rdoc_simple_gate_required_program=src/app/test/renderdoc_vulkan_widget_capture.spl`,
the generated fixture path, Vulkan runtime metadata, and `.rdc` `RDOC` magic.
The widget goal still remains incomplete until Electron Chromium/Vulkan also
produces widget `.rdc` evidence with nonblank ARGB proof.

Linux browser diagnostics:

- Before browser RenderDoc work, check RenderDoc's user-level Vulkan layer
  registration:

```sh
/opt/renderdoc/bin/renderdoccmd vulkanlayer --explain
/opt/renderdoc/bin/renderdoccmd vulkanlayer --register --user
```

  The repo evidence wrappers still create per-run layer manifests with
  `VK_LAYER_PATH`, but the installed RenderDoc tools and target-control paths
  can report an unregistered layer separately. Registration is host setup only;
  it is not passing evidence. On the current Linux host, user registration is
  fixed but Chrome and Electron browser `.rdc` gates still fail.
- The browser RenderDoc launch contract includes `--no-zygote` so RenderDoc
  child-process handling does not also have to cross Chromium's zygote model.
  This is required evidence metadata, but it is not sufficient by itself: Chrome
  still records GPU-process `exit_code=139` and no `.rdc` on the current host.
  The launch contract also requests
  `--enable-features=Vulkan,DefaultANGLEVulkan,VulkanFromANGLE`,
  `--ignore-gpu-blocklist`, and `--enable-gpu-rasterization`; the wrapper must
  launch those same flags, not only print them as metadata.
- Do not use `--in-process-gpu` as the browser Vulkan capture solution on this
  host. The older `/home/yoon/electron-vulkan` recipe used it, but current
  Chromium/Electron reports `Vulkan not supported with in process gpu` and the
  repo Electron runner segfaults under RenderDoc before `.rdc` output.
- Direct Chrome/Electron RenderDoc capture supports
  `RDOC_RENDERDOC_HOOK_CHILDREN=0` to omit `--opt-hook-children`. Use it only as
  a diagnostic control:

```sh
RDOC_RENDERDOC_HOOK_CHILDREN=0 scripts/tool/renderdoc-evidence.shs capture-html
RDOC_RENDERDOC_HOOK_CHILDREN=0 scripts/tool/renderdoc-evidence.shs capture-electron-html
```

  On the current Linux host, this avoids the Chrome GPU-process `exit_code=139`
  seen with child-process hooking, but it still produces `missing-rdc` because
  Chromium's Vulkan work happens in the GPU child process. Passing browser
  evidence still requires a valid `.rdc` with `RDOC` magic from the browser GPU
  process; no-child-hook runs are not passing gate evidence.
- `renderdoccmd inject --PID=<gpu-process>` is not a viable workaround on this
  host; RenderDoc reports that injecting into an already-running process is not
  supported on non-Windows systems.
- Running Chrome with only `VK_LAYER_RENDERDOC_Capture`,
  `ENABLE_VULKAN_RENDERDOC_CAPTURE=1`, and `RENDERDOC_CAPFILE` avoids the
  immediate Chromium GPU-process `exit_code=139` seen under
  `renderdoccmd capture --opt-hook-children`, but the current automated F12
  trigger does not produce `.rdc`. Treat this as diagnostic evidence, not as a
  passing gate. Reproduce with:

```sh
sh scripts/check/check-renderdoc-chrome-x11-layer-hotkey.shs
```

  The probe records the Chrome fixture window id, Chromium GPU process pid,
  hotkey attempts, and any `.rdc` magic in
  `build/renderdoc/chrome-x11-layer-hotkey/evidence.env`.
  RenderDoc source shows `RENDERDOC_CAPOPTS` is a byte-wise hex encoding of
  `CaptureOptions` using `a..p` nibbles. The local x86_64 default option string
  is `ababaaaaaaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaaaaaaa`; enabling
  `refAllResources` and `captureAllCmdLists` gives
  `ababaaaaaaaaaaaaaaaaaaaaaaaaabababaaaaaaaaaaaaaa`. On this host, running:

```sh
BUILD_DIR=build/renderdoc/chrome-x11-layer-hotkey-capopts \
RDOC_CAPOPTS=ababaaaaaaaaaaaaaaaaaaaaaaaaabababaaaaaaaaaaaaaa \
  sh scripts/check/check-renderdoc-chrome-x11-layer-hotkey.shs
```

  still records `missing-rdc`, despite a live `--use-angle=vulkan` GPU process
  and a targeted fixture window.
- GPU-process delayed autocapture is available through
  `RDOC_CHROME_GPU_AUTOCAPTURE=1`/`RDOC_ELECTRON_GPU_AUTOCAPTURE=1` plus
  `RDOC_GPU_LAUNCHER_DELAY_START_MS=<ms>`. It starts a background trigger
  thread inside the Chromium GPU process after launch. On this Linux host, the
  no-dlopen mode avoids the immediate startup crash but cannot obtain a usable
  RenderDoc API; explicitly preloading `librenderdoc.so` reintroduces
  GPU-process `exit_code=139`.
  Electron visible-window diagnostics can be enabled with
  `RDOC_ELECTRON_SHOW_WINDOW=1`, which forwards
  `ELECTRON_CAPTURE_SHOW_WINDOW=1` to the helper. This is diagnostic only: the
  current visible/data-url probes reach Electron load/settle/capture stages but
  still do not produce `.rdc`.
- The GPU-process autocapture shim also supports a loader-lock-free RenderDoc
  API lookup for Chromium:

```sh
RDOC_CHROME_GPU_AUTOCAPTURE=1 \
RDOC_GPU_LAUNCHER_ALLOW_DLOPEN=1 \
RDOC_GPU_LAUNCHER_NO_DLOPEN_FALLBACK=1 \
RDOC_GPU_LAUNCHER_DISABLE_DLSYM_WRAP=1 \
RDOC_GPU_LAUNCHER_TRIGGER_ONLY=1 \
  scripts/tool/renderdoc-evidence.shs capture-html
```

  This mode finds `RENDERDOC_GetAPI` by reading the loaded
  `librenderdoc.so` ELF dynsym and avoids `dlsym(RTLD_DEFAULT, ...)` and
  `dlopen(...)`, both of which can hang in the Chromium GPU process. On this
  host it reaches `rdoc_autocapture_api=ready`, but `TriggerCapture()` still
  does not produce `.rdc`; treat it as diagnostic until an `.rdc` with `RDOC`
  magic is present.
  If `RDOC_GPU_LAUNCHER_START_ON_DLSYM=1` sees `vkGetInstanceProcAddr` before
  `librenderdoc.so` is loaded, the evidence records
  `rdoc_autocapture_api=missing-librenderdoc`. Allowing a normal `dlopen` can
  stall inside `dlopen-path-start`; preloading RenderDoc makes the Electron GPU
  process crash with `exit_code=139`. These are blocker diagnostics, not passing
  capture modes.
  A delayed no-dlopen GPU-process trigger can find the already-loaded
  RenderDoc API (`rdoc_autocapture_api=ready`) and call
  `StartFrameCapture`/`EndFrameCapture`, but current Electron evidence returns
  `rdoc_autocapture_end=delay ok=0` with zero submit/present/swap counters and
  no `.rdc`.
- The autocapture shim wraps ANGLE scheduling symbols
  `EGL_PrepareSwapBuffersANGLE` and `EGL_WaitUntilWorkScheduledANGLE` in both
  upper- and lower-case spellings. On the current host Chromium resolves those
  function pointers, but the wrappers are not called before the Electron runner
  exits or times out; they remain diagnostics, not passing evidence.
- `tools/electron-live-bitmap/renderdoc_display_html.js` is a visible-window
  diagnostic runner that avoids `capturePage()`. It can hold a page open while
  the GPU-process shim triggers RenderDoc. Current runs against both the full
  fixture and a tiny animated HTML page still time out in Electron load and
  produce no `.rdc`, even though the RenderDoc API is available in the GPU
  process.
- The GPU launcher exports `RENDERDOC_CAPFILE` before the Vulkan layer
  initializes and forwards `RDOC_GPU_LAUNCHER_CAPOPTS` to `RENDERDOC_CAPOPTS`
  when set. Use this when checking whether a failure is caused by late
  in-application path setup:

```sh
RDOC_CHROME_GPU_AUTOCAPTURE=1 \
RDOC_CHROME_APP_MODE=1 \
RDOC_GPU_LAUNCHER_ALLOW_DLOPEN=1 \
RDOC_GPU_LAUNCHER_NO_DLOPEN_FALLBACK=1 \
RDOC_GPU_LAUNCHER_CAPOPTS=ababaaaaaaaaaaaaaaaaaaaaaaaaabababaaaaaaaaaaaaaa \
RDOC_AUTOCAPTURE_TRACE_PROC_NAMES=1 \
RDOC_AUTOCAPTURE_START_EGL_VK_LOCK=1 \
RDOC_AUTOCAPTURE_END_EGL_VK_UNLOCK=2 \
  scripts/tool/renderdoc-evidence.shs capture-html
```

  `RDOC_CHROME_APP_MODE=1` keeps the generated fixture open as a Chrome app on
  X11 instead of using screenshot mode. The autocapture shim can trace
  `dlsym`, `eglGetProcAddress`, Vulkan proc lookup, submit/present,
  `eglSwapBuffers`, and ANGLE's `eglLockVulkanQueueANGLE` /
  `eglUnlockVulkanQueueANGLE` extension calls. This remains diagnostic only:
  current Chrome evidence looks up the EGL/ANGLE Vulkan symbols but still does
  not execute a wrapped submit/present/swap/lock call in the GPU process or
  produce `.rdc`.
- The Chrome target-control diagnostic wraps `qrenderdoc --ui-python` in an
  outer timeout. If qrenderdoc's UI Python startup hangs, the script now records
  `target-control-no-evidence` instead of leaving the lane running indefinitely:

```sh
sh scripts/check/check-renderdoc-chrome-target-control.shs
```
- Running Electron with only the RenderDoc Vulkan layer currently times out
  before ARGB output and produces no `.rdc`; the canonical Electron gate still
  requires `tools/electron-live-bitmap/capture_html_argb.js` ARGB proof plus
  `.rdc` magic `RDOC`.
- Electron capture output and stage log paths are passed to the Electron process
  as absolute paths. Electron may resolve relative paths from its binary
  directory, so relative ARGB paths can produce misleading
  `missing-electron-argb-file` metadata even when the script printed a capture
  line. The canonical Electron gate should now show `rdoc_electron_argb_status=pass`
  when the bitmap exists; the browser `.rdc` gate remains separate.
- For focused Electron diagnostics, the ARGB helper accepts stage and fallback
  controls:

```sh
ELECTRON_CAPTURE_STAGE_LOG=build/renderdoc/electron-stage.log \
ELECTRON_CAPTURE_LOAD_TIMEOUT_MS=3000 \
ELECTRON_CAPTURE_FORCE_DATA_URL=1 \
ELECTRON_CAPTURE_CONTINUE_AFTER_LOAD_TIMEOUT=1 \
ELECTRON_CAPTURE_OFFSCREEN_PAINT=1 \
RDOC_ELECTRON_GPU_AUTOCAPTURE=1 \
RDOC_GPU_LAUNCHER_ALLOW_DLOPEN=1 \
RDOC_GPU_LAUNCHER_NO_DLOPEN_FALLBACK=1 \
RDOC_GPU_LAUNCHER_DISABLE_DLSYM_WRAP=1 \
RDOC_GPU_LAUNCHER_TRIGGER_ONLY=1 \
  scripts/tool/renderdoc-evidence.shs capture-electron-html
```

  This is a diagnostic path, not a passing gate. It records which Electron
  operation blocks under RenderDoc injection. On the current Linux host,
  `loadFile(...)` and `loadURL(data:)` time out, continuation reaches DOM audit
  and geometry, `capturePage(...)` hangs, and offscreen paint reaches
  `missing-offscreen-paint`. The gate remains failed until the evidence env
  records a valid Electron `.rdc` with `RDOC` magic and a nonblank ARGB file.

## macOS Notes

macOS does not provide native Vulkan drivers. Use the LunarG Vulkan SDK with
MoltenVK, or another Metal-backed Vulkan portability implementation, when
testing the Simple Vulkan path on macOS.

The current GUI/web/2D Vulkan comparison runbook is macOS-only until Windows
and Linux host runbooks validate the same evidence keys. Prepare a Homebrew
host with:

```sh
brew install vulkan-tools vulkan-loader vulkan-headers molten-vk spirv-tools glslang
vulkaninfo --summary
```

Then compare the Electron Chromium-backed baseline and the Simple GUI/web/2D
Vulkan path with the existing readiness/run helpers, and close the all-widget
RenderDoc proof with:

```sh
scripts/setup/setup-gui-web-2d-vulkan-env.shs --check
scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
sh scripts/check/check-gui-widget-renderdoc-goal-status.shs --strict
```

The setup helper resolves either an unpacked RenderDoc tree with
`bin/renderdoccmd` or a macOS `RenderDoc.app` bundle, and prints both
`LD_LIBRARY_PATH` and `DYLD_LIBRARY_PATH` exports for prepared capture hosts.

The shared CLI remains the preferred interface. On macOS, run the Simple lane
first and treat Chrome/Electron capture attempts as exploratory until their
Vulkan logs and RDOC gates both pass:

```sh
scripts/setup/setup-gui-web-2d-vulkan-env.shs --check
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
