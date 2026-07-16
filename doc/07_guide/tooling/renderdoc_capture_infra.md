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
RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/renderdoc/electron-implicit-layer-default-autocapture/electron-html/evidence.env \
  sh scripts/check/check-renderdoc-electron-html-gate.shs
PRODUCTION_GUI_WEB_RENDERER_PARITY_ENV=build/production_gui_web_renderer_parity_evidence/evidence.env \
  sh scripts/check/check-production-gui-web-renderer-parity-gate.shs
```

For repeated SSpec coverage of the aggregate audit, the wrapper uses a
fingerprinted nested-gate cache at
`build/gui-renderdoc-feature-coverage-static-cache` by default. Override
`GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR` to use a lane-local cache directory,
or set `GUI_RENDERDOC_AGGREGATE_DISABLE_DEFAULT_STATIC_CACHE=1` for a cold
operator refresh. The aggregate copies cached nested evidence into each scenario
build directory and keys RenderDoc-dependent gates by their evidence env paths.

For final GUI/Web/2D completion runs, use the stricter completion SSpec cache
mode: set `GUI_RENDERDOC_AGGREGATE_DISABLE_DEFAULT_STATIC_CACHE=1` and provide a
per-run `GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR`. Do not set
`GUI_RENDERDOC_AGGREGATE_READONLY_STATIC_CACHE_DIR` for final native-host
completion. Read-only seeded caches are acceptable for fast repeated contract
checks, but final Linux Vulkan, macOS Metal, Windows D3D12, mobile, and
production parity claims must be backed by fresh host artifacts copied into the
per-run output.

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
- `scripts/setup/setup-gui-web-2d-vulkan-env.ps1 --check` records Windows host
  readiness without installing tools or launching GUI apps. It consumes the
  latest Simple Vulkan readback evidence when present, checks `vulkaninfo`,
  `glslangValidator`, `spirv-as`, `dxc`, Chrome, Electron, and RenderDoc
  commands, and writes compatible `gui_web_2d_vulkan_*` rows. Use
  `--print-install` for Windows install hints; do not claim RenderDoc capture
  until `renderdoccmd` is present and a valid `.rdc` artifact is produced.

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
  `rt_renderdoc_*` extern table. Focused evidence reruns may set this to an
  already-built `src/compiler_rust/target/release/simple` when that binary is
  current and the lane is only refreshing capture artifacts.

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

Real platform validation is tracked through
`doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md` and
the active completion matrix in
`doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md`.
Those plans split the native-host packets for Linux Vulkan, macOS Metal, and
Windows D3D12/PIX. This guide documents shared capture formats, wrappers, and
gates only; do not use the current prep lane as completion evidence for any
real host.

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
viewport-matching and nonblank, and the Simple evidence env proves the Vulkan
backend before making a GUI/web/2D Vulkan comparison claim. The Simple backend
row is fail-closed: it only reaches `pass` when the same env also carries
`vulkan_engine2d_readback_validation_status=pass`, zero clear/rect mismatches,
`vulkan_engine2d_readback_blur_or_tolerance_used=false`, and passing
Vulkan-strict plus CPU/Vulkan parity exit codes.
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
pixels, `gui_showcase_4k_200fps_nonzero_pixels_status=pass`, target FPS met,
nonempty checksum, `gui_showcase_4k_200fps_checksum_status=pass`,
`frame_avg_ns`, `frame_p50_ns`, `frame_p95_ns`,
`gui_showcase_4k_200fps_log_file_status=pass`,
`gui_showcase_4k_200fps_time_log_file_status=pass`,
`retained-static-frame`,
`gui_showcase_4k_200fps_retained_render_mode_status=pass`, one redraw frame,
`gui_showcase_4k_200fps_retained_redraw_status=pass`, at least 200 measured frames, and
`target_fps >= 200`, plus RSS budget status with `max_rss_kb` and
`max_rss_budget_kb`. A pass row must also retain binary provenance:
`source_revision`, `source_revision_kind=content-sha256`,
`source_revision_files`, `simple_bin`, `use_native=1`,
`native_build_mode=aggressive-native`, and `fallback_state=none`. The
aggregate compares each retained row against a current content hash of the
retained perf wrapper and measured showcase source, then emits
`gui_showcase_4k_200fps_current_source_revision`,
`gui_showcase_4k_200fps_source_revision_status`,
`gui_showcase_8k_perf_current_source_revision`, and
`gui_showcase_8k_perf_source_revision_status`; use
`GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1` for release or goal evidence
that must fail stale perf rows instead of reporting them as reusable
diagnostics. Docs-only commits should not stale retained perf evidence unless
the measured wrapper/source content changes. The default wrapper budget is
262144 KiB for 4K and
750000 KiB for 8K; rows with `rss_status=measured` are diagnostics, not
completion evidence. The 8K row must likewise prove
`7680x4320`, `33177600` pixels, nonzero readback pixels,
`gui_showcase_8k_perf_nonzero_pixels_status=pass`, target FPS at least
200, positive measured frame count, checksum,
`gui_showcase_8k_perf_checksum_status=pass`,
`frame_avg_ns`, `frame_p50_ns`, `frame_p95_ns`,
`gui_showcase_8k_perf_log_file_status=pass`,
`gui_showcase_8k_perf_time_log_file_status=pass`,
`gui_showcase_8k_perf_retained_render_mode_status=pass`,
`gui_showcase_8k_perf_retained_redraw_status=pass`, RSS budget status, and the
same native binary provenance fields. Interpreter or fallback rows remain useful
diagnostics, but they are not 4K/8K completion evidence.
The aggregate validates producer-side native artifact proof for completion rows:
missing alias source, native binary, native executable bit, recognized native
binary format, or native build log status turns an otherwise passing retained
4K/8K row into a native-artifact failure. Explicit producer-side `pass` claims
are verified against the referenced files; a chmodded text file or stale status
row cannot satisfy native binary proof without actual ELF, Mach-O, or PE magic.
Symlinked or hardlinked retained showcase logs, time logs, alias sources,
native binaries, and native build logs are rejected as substituted artifacts;
the aggregate reports typed `symlink` or `hardlink` file statuses in the
matching `gui_showcase_*` rows. The retained perf producer also emits typed
`symlink` or `hardlink` statuses for those artifact fields, so linked evidence
is visible before the aggregate recomputes the file checks.
Producer-side wrapper rows include
`*_alias_src_file_status`, `*_native_bin_file_status`, and
`*_native_bin_executable_status`, `*_native_bin_format_status`, and
`*_native_build_log_file_status` so a reviewer can distinguish a planned probe
route from a completed native binary measurement with a runnable ELF, Mach-O,
or PE binary and retained build log.
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
For final completion, pair the explicit per-run cache with
`GUI_RENDERDOC_AGGREGATE_DISABLE_DEFAULT_STATIC_CACHE=1`; otherwise the default
shared cache remains a fast-lane optimization, not proof that the current host
just produced platform capture evidence.
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
recomputes that status for older evidence before accepting proof. Producer
source statuses are typed: `pass` means a regular single-link proof file, while
`symlink`, `hardlink`, `empty`, `not-regular`, and `missing` force the Electron
or Chrome child browser-backing row to fail. The setup producer delegates this
classification to `scripts/check/gui-web-2d-vulkan-browser-backing-status.js`
so the same status logic can be tested without launching a GUI host.
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
For Linux browser RenderDoc diagnostics, the Chromium GPU launcher writes child
stdout/stderr and shim telemetry to `gpu-launcher.log`. Evidence envs from
`capture-html` and `capture-electron-html` expose
`rdoc_chromium_gpu_launcher_angle_status`,
`rdoc_chromium_gpu_launcher_angle_error_count`,
`rdoc_gpu_launcher_clear_renderdoc_layer`,
`rdoc_gpu_launcher_vk_instance_layers`,
`rdoc_gpu_autocapture_status`,
`rdoc_gpu_autocapture_egl_get_platform_display_count`,
`rdoc_gpu_autocapture_egl_initialize_count`,
`rdoc_gpu_autocapture_egl_initialize_return_count`,
`rdoc_gpu_autocapture_egl_initialize_success_count`,
`rdoc_gpu_autocapture_egl_initialize_fail_count`,
`rdoc_gpu_autocapture_egl_initialize_last_result`,
`rdoc_gpu_autocapture_egl_initialize_last_error`,
`rdoc_gpu_autocapture_egl_choose_config_count`,
`rdoc_gpu_autocapture_vk_enum_instance_layer_count`,
`rdoc_gpu_autocapture_vk_enum_instance_extension_count`,
`rdoc_gpu_autocapture_vk_create_instance_count`, and
`rdoc_gpu_autocapture_vk_create_device_count`. The diagnostic
`RDOC_GPU_LAUNCHER_CLEAR_RENDERDOC_LAYER=1` deliberately clears the RenderDoc
Vulkan layer before GPU-child exec; use it only to isolate layer interaction,
never as browser `.rdc` completion evidence.

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
GUI_WEB_2D_VULKAN_ENV=build/gui-web-2d-vulkan-env-run-current/evidence.env \
GUI_WEB_2D_VULKAN_BROWSER_BACKING_EVIDENCE_ENV=build/gui-web-2d-vulkan-env-browser-backing/evidence.env \
sh scripts/check/check-linux-vulkan-render-log-compare.shs
```

By default this Linux row consumes the focused RenderDoc evidence paths:

- `build/gui-web-2d-vulkan-env-renderdoc-simple/renderdoc/simple/evidence.env`
- `build/renderdoc/chrome-implicit-layer-default-autocapture/html/evidence.env`
- `build/renderdoc/electron-implicit-layer-default-autocapture/electron-html/evidence.env`

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
pass. It also validates the Simple, Chrome, and Electron ARGB source rows
directly: each source must report a positive viewport size, positive nonblank
pixel count, and the three viewport dimensions must match before the Linux row
can pass. A bare `pairwise-argb-diff` pass without comparable nonblank source
rows is rejected. Missing RenderDoc `.rdc` evidence is reported through
`linux_vulkan_render_log_compare_renderdoc_*_status` plus the matching
`linux_vulkan_render_log_compare_renderdoc_*_reason`,
`linux_vulkan_render_log_compare_renderdoc_*_env_file_status`,
`linux_vulkan_render_log_compare_renderdoc_*_artifact_file_status`, and
`linux_vulkan_render_log_compare_renderdoc_*_artifact_magic`; by default Simple,
Chrome, and Electron RenderDoc rows must pass with real `.rdc` files and `RDOC`
magic in the first four artifact bytes. Env metadata that merely claims
`rdoc_capture_magic=RDOC` is not completion proof; `env_file_status=pass` plus
`artifact_file_status=missing` means the diagnostic env exists but the native
capture artifact still has not been produced. If the Linux compare env is
missing, `linux_vulkan_render_log_compare_pairwise_status=missing` names the
missing direct-run pixel-comparison row. `artifact_magic=missing` means no
native capture artifact was available to inspect, and `artifact_magic=invalid`
means an artifact exists but its first four bytes are not `RDOC`. If the Linux compare env is
absent, the aggregate reports each Simple/Chrome/Electron RenderDoc source as
`status=unavailable`, `env_file_status=missing`, and
`artifact_file_status=missing` instead of leaving those detail rows blank. Set
`LINUX_VULKAN_RENDER_LOG_REQUIRE_RDOC=0` only for diagnostic
partial-log inspection, and never use that mode to claim Linux platform-matrix
completion.
For browser RenderDoc blockers, the Linux compare env forwards the GPU-child
diagnostics from the Chrome and Electron evidence envs:
`linux_vulkan_render_log_compare_renderdoc_chrome_gpu_launcher_angle_status`,
`linux_vulkan_render_log_compare_renderdoc_chrome_gpu_launcher_angle_error_count`,
`linux_vulkan_render_log_compare_renderdoc_chrome_gpu_launcher_clear_renderdoc_layer`,
`linux_vulkan_render_log_compare_renderdoc_chrome_gpu_launcher_vk_instance_layers`,
`linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_status`,
`linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_api`,
`linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_started`,
`linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_finished`,
`linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_start_source`,
`linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_end_source`,
`linux_vulkan_render_log_compare_renderdoc_chrome_egl_get_platform_display_count`,
`linux_vulkan_render_log_compare_renderdoc_chrome_egl_initialize_count`,
`linux_vulkan_render_log_compare_renderdoc_chrome_egl_initialize_return_count`,
`linux_vulkan_render_log_compare_renderdoc_chrome_egl_initialize_success_count`,
`linux_vulkan_render_log_compare_renderdoc_chrome_egl_initialize_fail_count`,
`linux_vulkan_render_log_compare_renderdoc_chrome_egl_initialize_last_result`,
`linux_vulkan_render_log_compare_renderdoc_chrome_egl_initialize_last_error`,
`linux_vulkan_render_log_compare_renderdoc_chrome_egl_choose_config_count`,
`linux_vulkan_render_log_compare_renderdoc_chrome_vk_enum_instance_layer_count`,
`linux_vulkan_render_log_compare_renderdoc_chrome_vk_enum_instance_extension_count`,
`linux_vulkan_render_log_compare_renderdoc_chrome_vk_create_instance_count`, and
`linux_vulkan_render_log_compare_renderdoc_chrome_vk_create_device_count`, with
matching `...renderdoc_electron...` fields. These fields preserve whether the
GPU-process shim reached the RenderDoc API and capture start/end calls, plus
the current Linux diagnosis that browser GPU children can enumerate Vulkan
layers and extensions, enter `eglInitialize`, and still fail to produce `.rdc`
before `eglInitialize` returns or `vkCreateInstance` is reached.
When this pattern is present, the row emits
`linux_vulkan_render_log_compare_renderdoc_linux_angle_workaround_status=needed`
with reason
`linux-angle-eglinitialize-does-not-return-under-renderdoc-layer`. ANGLE's
upstream debugging guide documents `RENDERDOC_HOOK_EGL=0` as a Windows-only
workaround and says Linux requires a RenderDoc build without GL/GLES support
for this class of capture issue. The local installed RenderDoc still reports
the same non-returning `eglInitialize` behavior with `RENDERDOC_HOOK_EGL=0`;
see `doc/09_report/renderdoc_browser_linux_angle_egl_hook_2026-06-29.md`.
For Linux, `scripts/setup/build-renderdoc-linux-vulkan-only.shs` builds
RenderDoc with `ENABLE_GL=OFF`, `ENABLE_GLES=OFF`, `ENABLE_EGL=OFF`, and
`ENABLE_VULKAN=ON` into `build/tools/renderdoc-linux-vulkan-only`. The wrapper
can use an extracted local dev-package sysroot at
`build/tools/renderdoc-local-sysroot` through `RENDERDOC_LOCAL_SYSROOT`, so
missing `libxcb-keysyms1-dev` or `libx11-xcb-dev` headers can be supplied
without root access. The shared RenderDoc finder prefers this tree when present.
Current July 2 evidence from
`build/renderdoc/chrome-vulkan-only-egl-direct-20260702` shows Chrome reaches
`rdoc_autocapture_egl_get_platform_display`,
`rdoc_autocapture_egl_initialize`, WSI-enabled `vkCreateInstance`, and emits
`gpu_chrome_capture.rdc` with `RDOC` magic under the Vulkan-only build.
Electron remains a separate loader/harness blocker: the focused
`electron-vulkan-only-*` probes time out before the GPU launcher log exists,
with `electron_capture_stage=load-file-failed` and no `.rdc`.
Browser GPU-child capture must force both `VK_LAYER_PATH` and
`VK_IMPLICIT_LAYER_PATH` to the generated per-run `vulkan-layer.d` directory.
`VK_LAYER_PATH` alone is not enough for RenderDoc because the Vulkan loader can
still choose a globally registered implicit layer before the run-local
Vulkan-only manifest. The GPU-autocapture launcher defaults to the
loader-lock-free ELF lookup for `RENDERDOC_GetAPI` and disables the `dlopen`
fallback for this route. The default aggregate gate must still require both
Chrome and Electron `.rdc` magic; Chrome has passing Vulkan-only focused
evidence, while Electron is not yet passing.
For diagnostic Chromium flag variants, the shared flag helpers accept
`RDOC_CHROME_EXTRA_VULKAN_FLAGS` and `RDOC_ELECTRON_EXTRA_VULKAN_FLAGS`.
These variables append to the browser-specific Vulkan launch flags without
changing the canonical defaults. A 2026-06-29 `--use-gl=angle` probe still
failed before `eglInitialize` returned and before `vkCreateInstance`; see
`doc/09_report/renderdoc_browser_use_gl_angle_2026-06-29.md`.
The same row exposes host readiness fields before platform agents debug capture
failures:
`linux_vulkan_render_log_compare_host_renderdoc_status`,
`linux_vulkan_render_log_compare_host_renderdoc_tool`,
`linux_vulkan_render_log_compare_host_chrome_status`,
`linux_vulkan_render_log_compare_host_chrome_tool`,
`linux_vulkan_render_log_compare_host_electron_status`, and
`linux_vulkan_render_log_compare_host_electron_tool`. A `missing` host status is
not a renderer pass or fail by itself; it means the Linux GUI host must install
the named capture/browser tool before the `.rdc` blocker can be verified.
Bare relative `.rdc` artifact names resolve beside their evidence env file, so
a stale working-directory `frame.rdc` cannot satisfy Simple, Chrome, or Electron
RenderDoc proof.
For browser GPU-child capture attempts that need a trigger without interposing
EGL/Vulkan symbols, set `RDOC_GPU_LAUNCHER_DELAY_TRIGGER=1`. This uses
`scripts/tool/renderdoc-delay-trigger.c`, a minimal preload shim that locates
`RENDERDOC_GetAPI` with a loader-lock-free ELF lookup. By default it calls
timed `StartFrameCapture`/`EndFrameCapture`; with
`RDOC_GPU_LAUNCHER_DELAY_TRIGGER_MODE=trigger`, it calls `TriggerCapture()`
instead. Current Chrome and Electron evidence against the Vulkan-only RenderDoc
build reaches the API but reports zero captures for both modes:
`rdoc_gpu_delay_trigger_last_end_ok=0`,
`rdoc_gpu_delay_trigger_is_capturing_after_start=0`,
`rdoc_gpu_delay_trigger_is_capturing_after_trigger=0`, and
`rdoc_gpu_delay_trigger_num_captures_after=0`, so no `.rdc` is produced.
`RDOC_GPU_LAUNCHER_DELAY_TARGET_DEVICE=1` attempts to derive a
`RENDERDOC_DevicePointer` by intercepting `vkCreateInstance`, but current
Chrome/Electron runs report `rdoc_gpu_delay_trigger_vk_create_instance_count=0`
and `rdoc_gpu_delay_trigger_target_device=(nil)`, so Chromium/ANGLE is not
exposing its Vulkan instance through this LD_PRELOAD path; see
`doc/09_report/renderdoc_browser_delay_trigger_vulkan_only_2026-06-29.md`.
The Linux row also emits structured blocker fields for parallel platform
agents:
`linux_vulkan_render_log_compare_blocked_gate_count`,
`linux_vulkan_render_log_compare_blocked_gates`,
`linux_vulkan_render_log_compare_simple_vulkan_gate_status`,
`linux_vulkan_render_log_compare_browser_backing_gate_status`,
`linux_vulkan_render_log_compare_pairwise_gate_status`,
`linux_vulkan_render_log_compare_argb_source_gate_status`, and
`linux_vulkan_render_log_compare_renderdoc_gate_status`. Use these fields
instead of parsing `linux_vulkan_render_log_compare_reason` when deciding
whether the Linux blocker is backend selection, browser Vulkan backing,
pairwise pixels, ARGB source evidence, or RenderDoc `.rdc` capture.

Current Linux host evidence on 2026-06-25 has
`linux_vulkan_render_log_compare_pairwise_status=pass`, Simple RenderDoc
`pass`, Chrome RenderDoc `fail`, and Electron RenderDoc `fail`. Current focused
browser backing passes, but the row remains failed because the required Chrome
and Electron native RenderDoc lanes are still not pass; do not treat passing
pairwise ARGB or browser-GPU proof as RenderDoc completion.

Absent macOS Metal and Windows D3D12 compare env files stay classified as
missing platform rows, but the aggregate still emits explicit details for
parallel agents: macOS uses `pairwise_status=missing`,
`gpu_capture_status=unavailable`, and `gpu_capture_artifact*=missing`; Windows
uses `pairwise_status=missing`, `pix_status=unavailable`,
`pix_artifact*=missing`, `gpu_debugger_status=unavailable`, and
`gpu_debugger_artifact=missing`. Blank fields in those rows are regressions.

Completion keys:

```text
linux_vulkan_render_log_compare_status=pass
linux_vulkan_render_log_compare_required_api=vulkan
linux_vulkan_render_log_compare_pairwise_status=pass
linux_vulkan_render_log_compare_renderdoc_simple_status=pass
linux_vulkan_render_log_compare_renderdoc_simple_reason=pass
linux_vulkan_render_log_compare_renderdoc_simple_env_file_status=pass
linux_vulkan_render_log_compare_renderdoc_simple_artifact_file_status=pass
linux_vulkan_render_log_compare_renderdoc_simple_artifact_magic=RDOC
linux_vulkan_render_log_compare_renderdoc_chrome_status=pass
linux_vulkan_render_log_compare_renderdoc_chrome_reason=pass
linux_vulkan_render_log_compare_renderdoc_chrome_env_file_status=pass
linux_vulkan_render_log_compare_renderdoc_chrome_artifact_file_status=pass
linux_vulkan_render_log_compare_renderdoc_chrome_artifact_magic=RDOC
linux_vulkan_render_log_compare_renderdoc_electron_status=pass
linux_vulkan_render_log_compare_renderdoc_electron_reason=pass
linux_vulkan_render_log_compare_renderdoc_electron_env_file_status=pass
linux_vulkan_render_log_compare_renderdoc_electron_artifact_file_status=pass
linux_vulkan_render_log_compare_renderdoc_electron_artifact_magic=RDOC
```

The source logs use `simple-render-log-v1` and include
`simple_render_log_reason` for normalized failure detail and
`simple_render_log_native_info` for native-only metadata that does not yet fit
the normalized schema. They also expose original native provenance:
`simple_render_log_original_capture_tool`,
`simple_render_log_original_native_log_format`, and
`simple_render_log_original_native_log_source`. Current formats include
`renderdoc-rdc`, `renderdoc-diagnostic`, `xcode-gputrace`, `pix-capture`,
`gpu-debugger-log`, and `browser-gpu-metadata`. Metal, D3D12/PIX, GPU
debugger, and Tauri mobile lanes must keep this schema and add native sidecar
fields instead of inventing unrelated key names. If any required render-log or
native capture field is missing, completion remains `incomplete`.

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
Frame Capture evidence is expected. Strict capture mode requires
`macos_metal_gpu_capture_artifact` and
`macos_metal_gpu_capture_artifact_magic=XCODE-GPUTRACE`; a status-only capture
row is diagnostic and does not prove native Metal GPU capture. Completion keys:

```text
macos_metal_render_log_compare_status=pass
macos_metal_render_log_compare_required_api=metal
macos_metal_render_log_compare_pairwise_status=pass
macos_metal_render_log_compare_gpu_capture_status=pass
```

`check-gui-renderdoc-feature-coverage-status.shs` preserves those macOS detail
rows in the aggregate evidence and report. A passing aggregate macOS row must
also carry `XCODE-GPUTRACE`, passing Electron/Chrome/browser Metal backing,
`pairwise-argb-diff`, all three pairwise diff lanes, passing ARGB source
reasons, and a passing ARGB viewport reason.

The gate rejects missing Metal submit/readback, missing raw framebuffer
download, checksum mismatch, browser fallback, and non-pairwise comparisons.
It also rejects reused proof inputs: Chrome and Electron browser-backing
metadata must resolve to distinct source files, and the Simple, Chrome, and
Electron ARGB artifacts must resolve to distinct files rather than the same
capture copied under multiple evidence keys.
The macOS row also emits structured blockers:
`macos_metal_render_log_compare_blocked_gate_count`,
`macos_metal_render_log_compare_blocked_gates`,
`macos_metal_render_log_compare_generated_readback_gate_status`,
`macos_metal_render_log_compare_framebuffer_readback_gate_status`,
`macos_metal_render_log_compare_browser_backing_gate_status`,
`macos_metal_render_log_compare_pairwise_gate_status`,
`macos_metal_render_log_compare_argb_source_gate_status`, and
`macos_metal_render_log_compare_gpu_capture_gate_status`. Use these fields
instead of parsing the reason string when assigning a macOS blocker to native
Metal readback, browser Metal backing, pairwise pixels, ARGB source evidence,
or Xcode GPU Frame Capture.
For auditing the underlying Chrome/Electron/browser decision, the same env also
emits `macos_metal_render_log_compare_electron_browser_backing_status`,
`macos_metal_render_log_compare_chrome_browser_backing_status`,
`macos_metal_render_log_compare_browser_backing_status`, the three pairwise
diff lane statuses, the Simple/Chrome/Electron ARGB source plus viewport
reasons, `macos_metal_render_log_compare_browser_backing_source_duplicate_reason`,
and `macos_metal_render_log_compare_argb_artifact_duplicate_reason`.

macOS producer checklist:

- `METAL_GENERATED_2D_READBACK_ENV`: must report native Metal generated
  readback, a nonzero backend handle, framebuffer/readback dimensions, checksum
  or ARGB evidence, and `macos_metal_render_log_compare_required_api=metal`
  after aggregation.
- `METAL_ENGINE2D_FRAMEBUFFER_READBACK_ENV`: must report the Engine2D
  framebuffer download/readback artifact used for Simple-side comparison.
- `MACOS_METAL_BROWSER_ENV`: must contain distinct Chrome and Electron
  Metal-backed browser metadata plus ARGB artifacts, viewport rows, and
  pairwise diff inputs.
- Xcode capture source, when strict capture is enabled: must produce
  `macos_metal_gpu_capture_artifact` and
  `macos_metal_gpu_capture_artifact_magic=XCODE-GPUTRACE`; status-only rows are
  diagnostic.
- Completion handoff: run the compare wrapper, preserve the env/report, then
  feed that env into the aggregate GUI/Web/2D completion checker without
  replacing missing captures with copied or shared artifacts.

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
debugger capture is required. Strict mode requires either
`windows_d3d12_pix_capture_artifact` with
`windows_d3d12_pix_capture_artifact_magic=PIX`, or
`windows_d3d12_gpu_debugger_capture_artifact` for an equivalent debugger log.
Status-only debugger rows are diagnostic and do not prove native D3D12 capture.
PIX and GPU debugger artifacts must be regular, non-symlink, non-hardlink
files so strict evidence cannot be substituted through shared capture aliases.
Relative PIX/GPU-debugger artifact names resolve beside `WINDOWS_D3D12_PIX_ENV`
so stale working-directory files cannot satisfy strict Windows capture proof.
Rendering evidence scripts use GNU `stat -c '%h'` with BSD `stat -f '%l'`
fallback when counting links, so Linux-host verification catches hardlinked
artifacts instead of treating GNU `stat -f` filesystem output as a valid count.
The DirectX browser-backing setup uses
`scripts/check/gui-web-2d-directx-browser-backing-status.js` to classify
Electron and Chrome proof JSON paths before accepting child browser rows.

Windows producer checklist:

- `WINDOWS_D3D12_NATIVE_READBACK_ENV`: must report native D3D12 generated
  readback, device/backend identity, readback dimensions, and checksum or ARGB
  evidence accepted by the compare wrapper as D3D12, not D3D11.
- `WINDOWS_D3D12_BROWSER_ENV`: must contain distinct Chrome and Electron
  D3D12-backed browser metadata plus ARGB artifacts, viewport rows, and
  pairwise diff inputs.
- `WINDOWS_D3D12_PIX_ENV`: in strict mode must contain
  `windows_d3d12_pix_capture_artifact` with
  `windows_d3d12_pix_capture_artifact_magic=PIX`, or
  `windows_d3d12_gpu_debugger_capture_artifact` for the accepted equivalent
  debugger log. The artifact must be a regular unique file.
- Completion handoff: run the compare wrapper with
  `WINDOWS_D3D12_RENDER_LOG_REQUIRE_PIX=1` when GPU debugger proof is required,
  preserve the env/report, and pass that env into the aggregate GUI/Web/2D
  completion checker.
`*_browser_backing_proof_file_status=pass` means a regular, nonempty,
single-link proof file; `symlink`, `hardlink`, `empty`, `not-regular`, and
`missing` force the child row to fail.
Completion keys:

```text
windows_d3d12_render_log_compare_status=pass
windows_d3d12_render_log_compare_required_api=d3d12
windows_d3d12_render_log_compare_pairwise_status=pass
windows_d3d12_render_log_compare_blocked_gate_count=0
windows_d3d12_render_log_compare_blocked_gates=
windows_d3d12_render_log_compare_native_readback_gate_status=pass
windows_d3d12_render_log_compare_browser_backing_gate_status=pass
windows_d3d12_render_log_compare_pairwise_gate_status=pass
windows_d3d12_render_log_compare_argb_source_gate_status=pass
windows_d3d12_render_log_compare_pix_gpu_debugger_gate_status=pass
windows_d3d12_render_log_compare_pix_status=pass
windows_d3d12_render_log_compare_pix_artifact_file_status=pass
windows_d3d12_render_log_compare_pix_artifact_file_magic=PIX
windows_d3d12_render_log_compare_gpu_debugger_status=pass
windows_d3d12_render_log_compare_gpu_debugger_artifact_file_status=pass
```

The gate rejects D3D11-only evidence, missing PIX/GPU-debugger proof in strict
mode, browser fallback, and non-pairwise comparisons.
It also emits stable structured blockers:
`windows_d3d12_render_log_compare_blocked_gate_count`,
`windows_d3d12_render_log_compare_blocked_gates`,
`windows_d3d12_render_log_compare_native_readback_gate_status`,
`windows_d3d12_render_log_compare_browser_backing_gate_status`,
`windows_d3d12_render_log_compare_pairwise_gate_status`,
`windows_d3d12_render_log_compare_argb_source_gate_status`, and
`windows_d3d12_render_log_compare_pix_gpu_debugger_gate_status`. The aggregate
also forwards `windows_d3d12_render_log_compare_pix_artifact_file_status` and
`windows_d3d12_render_log_compare_gpu_debugger_artifact_file_status`; a
status-only PIX/GPU-debugger row without passing artifact file proof is not
completion evidence. Use these fields instead of parsing the reason string when
assigning a Windows blocker to native D3D12 readback, browser D3D12 backing,
pairwise ARGB diff, ARGB source evidence, or PIX/GPU-debugger capture. Failing
rows list blocked gate names such as `windows-d3d12-native-readback`,
`browser-d3d12-backing`, `pairwise-argb-diff`, `argb-source-evidence`, and
`pix-or-gpu-debugger`.

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
native_render_log_platform_matrix_linux_vulkan_command=BUILD_DIR=build/linux-vulkan-render-log-compare sh scripts/check/check-linux-vulkan-render-log-compare.shs
native_render_log_platform_matrix_macos_metal_command=MACOS_METAL_RENDER_LOG_REQUIRE_GPU_CAPTURE=1 BUILD_DIR=build/macos-metal-render-log-compare sh scripts/check/check-macos-metal-render-log-compare.shs
native_render_log_platform_matrix_windows_d3d12_command=WINDOWS_D3D12_RENDER_LOG_REQUIRE_PIX=1 BUILD_DIR=build/windows-d3d12-render-log-compare sh scripts/check/check-windows-d3d12-render-log-compare.shs
```

The aggregate revalidates each platform row before marking the matrix complete:
Linux must report `required_api=vulkan`, `pairwise_status=pass`, and pass
RenderDoc statuses for Simple, Chrome, and Electron. It also forwards
`linux_vulkan_render_log_compare_host_renderdoc_*`,
`linux_vulkan_render_log_compare_host_chrome_*`, and
`linux_vulkan_render_log_compare_host_electron_*` rows from the Linux leaf
wrapper, plus browser autocapture lifecycle rows such as
`linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_api`,
`..._started`, `..._finished`, `..._start_source`, and `..._end_source`, so
platform agents can distinguish missing host tools, missing RenderDoc API
startup, and failed capture artifacts. These host-tool and lifecycle rows are
readiness diagnostics; real `.rdc` artifact status and `RDOC` magic remain the
RenderDoc completion proof. macOS
must report `required_api=metal`, `pairwise_status=pass`, and GPU capture status
`pass`; Windows must report `required_api=d3d12`, `pairwise_status=pass`, PIX
status `pass`, zero blocked gates, passing native readback/browser
backing/pairwise ARGB/source/PIX-GPU-debugger gate statuses, and GPU debugger
status `pass`.
A stale or forged
`*_render_log_compare_status=pass` without those fields is downgraded to a
failed platform row.

If any platform compare evidence is missing or failing, the aggregate keeps
`gui_renderdoc_feature_coverage_status` incomplete and adds the native
render-log platform matrix to `blocked_completion_gates`.

On Linux and macOS, the wrapper uses a repo-local pure/self-hosted Simple
driver for the Simple Vulkan lane. The selected executable is recorded as
`gui_web_2d_vulkan_simple_bin`, with provenance in
`gui_web_2d_vulkan_simple_bin_selection_reason` and
`gui_web_2d_vulkan_simple_bin_status`. If `bin/simple` is missing in a linked
worktree, the wrapper falls back to repo release binaries under `release/**` or
`bin/release/**`, then a PATH `simple` only when the resolved executable belongs
to the same Git repository or `ALLOW_PATH_SIMPLE_BIN=1` was explicitly set. It
records `self-hosted-release`, `default-missing-same-repo-path-fallback`, or
`default-missing-path-opt-in` for those cases. Rust seed binaries under
`src/compiler_rust/**` are forbidden for this lane; explicit use is recorded as
`gui_web_2d_vulkan_simple_bin_status=forbidden` and is not executed. If no
fresh self-hosted driver exists, build/deploy one and rerun:

```sh
bin/simple bootstrap --release
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
- The Simple GUI/web/2D Vulkan comparison lane reports
  `vulkan_engine2d_readback_validation_status=pass`, clear and rect readback
  statuses `pass`, clear and rect mismatches `0`, no blur/tolerance fallback,
  and exit code `0` for both the Vulkan strict and CPU/Vulkan parity specs.
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
comparison gate on a matching native host. Run those validations in separate
sessions using the platform plans under `doc/03_plan/agent_tasks/`, then commit
each platform's evidence/report independently.

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
the 105/105 HTML tag coverage and 131/131 implemented CSS property coverage in
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
covered/total counts. The rendered implemented-CSS universe must come from
`html_css_rendering_manifest_traceability_css_property_source`, currently
`scripts/check/check-html-css-sspec-traceability.shs`, with
`html_css_rendering_manifest_traceability_css_property_source_status=pass` and
`html_css_rendering_manifest_traceability_css_property_source_count` matching
`html_css_rendering_manifest_traceability_css_property_count`; a local
hardcoded fixture-only property list is not valid completion evidence.
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
For direct readiness answers, consume
`html_css_full_rendering_goal_ready_status`,
`html_css_full_rendering_goal_all_html_elements_ready_status`,
`html_css_full_rendering_goal_all_implemented_css_ready_status`, and
`html_css_full_rendering_goal_all_css_properties_ready_status`. A pass for the
HTML or implemented-CSS readiness keys does not imply that all CSS properties
are ready; the full CSS readiness key must also be `pass`.
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
input, pointer, and click evidence. The aggregate also emits explicit
`*_file_status` rows for the HTML, ARGB, PNG, audit, interaction JSON,
interaction PNG, and interaction log artifacts so missing host output is visible
without inferring it from blank paths. The wrapper keeps the legacy artifact
keys and also emits canonical `*_path` aliases; aggregate checks consume the
canonical aliases. Direct wrapper runs only use PATH-based `simple` discovery
when `ALLOW_PATH_SIMPLE_CMD=1` is set; the aggregate nested Web WM run enables
that opt-in fallback so clean jj worktrees can use the installed Simple binary
without hardcoded host paths. `environment-unavailable` remains a useful host
diagnosis but is still reported as `modern Web WM Electron visual and
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
`gui_widget_renderdoc_goal_simple_gate_widget_html_bytes_status=pass`,
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
`gui_widget_renderdoc_goal_simple_gate_source_env`,
`gui_widget_renderdoc_goal_simple_gate_capture_command`,
`gui_widget_renderdoc_goal_simple_gate_source_env_file_status`,
`gui_widget_renderdoc_goal_simple_gate_capture_file_status`,
`gui_widget_renderdoc_goal_simple_gate_capture_file_magic`,
`gui_widget_renderdoc_goal_simple_gate_runtime_backend`,
`gui_widget_renderdoc_goal_simple_gate_widget_html_bytes`,
`gui_widget_renderdoc_goal_simple_gate_widget_html_bytes_status`,
`gui_widget_renderdoc_goal_simple_gate_fixture_path_status`,
`gui_widget_renderdoc_goal_simple_gate_required_backend`,
`gui_widget_renderdoc_goal_simple_gate_required_scene`,
`gui_widget_renderdoc_goal_simple_gate_required_program`,
`gui_widget_renderdoc_goal_simple_gate_required_html_path_suffix`,
`gui_widget_renderdoc_goal_simple_gate_required_magic`,
`gui_widget_renderdoc_goal_electron_gate_status`, and
`gui_widget_renderdoc_goal_electron_gate_reason`,
`gui_widget_renderdoc_goal_electron_gate_failure_class`,
`gui_widget_renderdoc_goal_electron_gate_source_env`,
`gui_widget_renderdoc_goal_electron_gate_capture_command`,
`gui_widget_renderdoc_goal_electron_gate_source_env_file_status`,
`gui_widget_renderdoc_goal_electron_gate_capture_file_status`,
`gui_widget_renderdoc_goal_electron_gate_capture_file_magic`,
`gui_widget_renderdoc_goal_electron_gate_argb_file_status`,
`gui_widget_renderdoc_goal_electron_gate_argb_status`,
`gui_widget_renderdoc_goal_electron_gate_argb_nonblank_pixel_count`,
`gui_widget_renderdoc_goal_electron_gate_requested_api`,
`gui_widget_renderdoc_goal_electron_gate_requested_angle`,
`gui_widget_renderdoc_goal_electron_gate_requested_features`,
`gui_widget_renderdoc_goal_electron_gate_fixture_path_status`, and
`gui_widget_renderdoc_goal_electron_gate_required_backend`,
`gui_widget_renderdoc_goal_electron_gate_required_scene`,
`gui_widget_renderdoc_goal_electron_gate_required_magic`,
`gui_widget_renderdoc_goal_electron_gate_required_html_path_suffix`, and
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
  `build/renderdoc/electron-implicit-layer-default-autocapture/electron-html/evidence.env` should report
  `rdoc_backend=electron`, `rdoc_scene=html-css-electron`,
  `rdoc_capture_status=pass`, `rdoc_capture_magic=RDOC`,
  `rdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html`,
  `rdoc_electron_capture_script=tools/electron-live-bitmap/renderdoc_display_html.js`
  or `tools/electron-live-bitmap/capture_html_argb.js`,
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
  evidence is not live renderer parity evidence. The wrapper exports the
  resolved self-hosted `SIMPLE_BIN` to nested parity checks and records
  `production_gui_web_renderer_parity_simple_bin` plus
  `production_gui_web_renderer_parity_simple_bin_source` and
  `production_gui_web_renderer_parity_simple_bin_status`. The Rust seed under
  `src/compiler_rust/` is `forbidden` for this production evidence path and is
  not executed; missing self-hosted binaries fail closed as `missing`. The nested
  Electron generated-GUI matrix subcheck records the same contract as
  `electron_generated_gui_web_simple_bin`,
  `electron_generated_gui_web_simple_bin_source`, and
  `electron_generated_gui_web_simple_bin_status`, which the parent parity
  evidence keeps under the `matrix_` prefix. The nested
  Electron/Simple layout manifest records this same contract as
  `electron_simple_web_layout_manifest_simple_bin`,
  `electron_simple_web_layout_manifest_simple_bin_source`, and
  `electron_simple_web_layout_manifest_simple_bin_status`; the parent parity
  evidence forwards those as
  `production_gui_web_renderer_parity_layout_manifest_simple_bin*`. The nested
  backend-executed parity subcheck records the same contract as
  `production_gui_backend_simple_bin`,
  `production_gui_backend_simple_bin_source`, and
  `production_gui_backend_simple_bin_status`, and the parent parity evidence
  forwards those as `production_gui_web_renderer_parity_backend_simple_bin*`.
  When `SIMPLE_BIN` is not set, the parent production wrapper chooses a
  host-compatible self-hosted Simple binary and skips stale cross-host release
  artifacts such as Linux ELF binaries on macOS; an explicit incompatible
  `SIMPLE_BIN` is recorded as `simple-bin-incompatible` instead of being
  executed by nested GUI probes.
  The nested Metal Engine2D framebuffer readback subcheck rejects the Rust seed
  the same way and records `metal_engine2d_framebuffer_readback_simple_bin`,
  `metal_engine2d_framebuffer_readback_simple_bin_source`, and
  `metal_engine2d_framebuffer_readback_simple_bin_status`; the parent parity
  evidence forwards those as
  `production_gui_web_renderer_parity_metal_readback_simple_bin*`, and the gate
  re-emits them under
  `production_gui_web_renderer_parity_gate_metal_readback_simple_bin*`.
  On non-Darwin hosts, Metal framebuffer readback is classified as
  `unavailable` with reason `metal-requires-macos`; this is not a Linux
  GUI/web hardening failure. On Darwin, the same subcheck remains strict and
  must prove the raw Metal framebuffer download path, the interpreter spec, and
  `blur_or_tolerance_used=false`.
  The parent production wrapper now runs the macOS Metal render-log compare
  whenever `production_gui_web_renderer_parity_metal_readback_status=pass`,
  even if the generic backend row still reports a fallback such as
  `production_gui_web_renderer_parity_backend_metal_resolved=vulkan-unavailable`.
  This keeps the log from hiding Electron/Chrome Metal-backed browser gaps
  behind `backend-not-metal`: the forwarded rows include
  `production_gui_web_renderer_parity_metal_render_log_backend_resolved`,
  `production_gui_web_renderer_parity_metal_render_log_metal_readback_status`,
  the browser backing gate, pairwise gate, ARGB source gate, and blocked-gate
  count. The gate wrapper re-emits the same values with the
  `production_gui_web_renderer_parity_gate_metal_render_log_*` prefix so
  downstream reports can distinguish Simple Metal readback from missing
  Electron/Chrome Metal browser proof. Simple Metal readback proves the Simple
  backend only; Electron/Chrome Metal-backed browser comparison is proven only
  by the macOS Metal render-log compare rows. Use
  `scripts/check/check-macos-metal-browser-backing-evidence.shs` on macOS to
  create `build/macos-metal-browser-backing/evidence.env`: it renders the stable
  `css_boxes.html` fixture through Simple Metal, Chrome DevTools with GPU
  enabled, and local Electron Chromium. Electron ARGB capture uses offscreen OSR
  exact-sRGB mode (`macos_metal_electron_capture_compositor_mode=offscreen-osr-exact-srgb`)
  so macOS display-compositor ICC transforms cannot alter the solid-color
  fixture, while Electron browser target GPU metadata still proves Metal backing.
  The wrapper writes scoped Metal GPU metadata source files and emits exact
  `pairwise-argb-diff` rows for Simple/Chrome/Electron ARGB artifacts. Then run
  `scripts/check/check-macos-metal-render-log-compare.shs` to validate the
  full normalized Metal log contract. The production parity wrapper forwards
  the compare's Tauri iOS/WKWebView rows, including
  `production_gui_web_renderer_parity_metal_render_log_require_tauri_ios`,
  `production_gui_web_renderer_parity_metal_render_log_tauri_ios_env_file_status`,
  and
  `production_gui_web_renderer_parity_metal_render_log_tauri_ios_env_artifact_status`,
  so strict mobile requirements are visible in the top-level evidence instead
  of only in the nested compare env.
  Font offload
  `unavailable` is recorded but does not satisfy the production parity wrapper.
  A font pass must also carry
  `production_gui_web_renderer_parity_font_offload_runtime_evidence_status=pass`
  from `PRODUCTION_GUI_FONT_RUNTIME_EVIDENCE_ENV`; by default
  `scripts/check/check-production-gui-font-offload-evidence.shs` now attempts
  to create that env through
  `scripts/check/check-production-gui-font-runtime-evidence.shs`. The runtime
  producer fails closed unless current vector-font compute evidence reports GPU
  returned glyphs and the selected Metal/CUDA/OpenCL generated-2D readback
  proof reports submit plus readback availability. On macOS, the Metal vector
  font producer emits `metal-vector-font-glyph-pixels-returned` and
  `production_gui_font_runtime_metal_*` rows after GPU glyph pixel readback;
  the wrapper forces interpreter mode for generated Simple CPU-oracle runs so
  JIT `spl_dlopen` failures cannot mask the backend proof. It also emits
  `production_gui_font_runtime_candidates_simple` so the font wrapper evaluates
  the backend that actually produced the source proof. Direct env-only
  readiness values are diagnostic inputs, not production completion evidence.
  Mobile renderer parity is checked with
  `scripts/check/check-tauri-mobile-renderer-parity-evidence.shs`. The Android
  lane uses `scripts/check/check-tauri-android-mobile-renderer-evidence.shs`,
  prepares `mobile_probe_entry.txt` with `mdi-smoke`, copies
  `examples/06_io/ui/tauri_mobile_mdi_smoke.spl` into the Tauri mobile entry,
  regenerates the UI bundle, runs `npm run prepare:dist`, and builds the debug
  APK by default before installing it on a live device or emulator. Completion
  requires the Android screenshot artifact, Vulkan/skiavk render-log marker,
  foreground `com.simple.ui` proof, and MDI event/capture/performance/animation
  rows all to pass. The Android wrapper freezes the background logcat stream
  before validator source-size checks, so a growing log cannot invalidate a real
  proof as a size mismatch.
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
  The surface manifest wrapper supports
  `TAURI_CHROME_LAYOUT_MANIFEST_RESUME=1` for interrupted evidence collection:
  it reuses accepted per-case `pass`/tracked-divergence evidence only when the
  row also carries the current ARGB artifact contract, including symlink and
  hardlink checks, exact viewport dimensions, nonzero pixels, and the expected
  Tauri or Chrome producer. It reruns failed, unavailable, missing, or stale
  artifact rows. When running through
  `scripts/check/check-production-gui-web-renderer-parity-evidence.shs`, use
  the production-level controls
  `PRODUCTION_GUI_WEB_RENDERER_PARITY_LAYOUT_ENV` to point at a completed
  Electron layout manifest when repairing only the surface lane,
  `PRODUCTION_GUI_WEB_RENDERER_PARITY_LAYOUT_TIMEOUT_SECS` when the full
  Electron/Simple layout manifest needs a larger outer budget than other
  subchecks,
  `PRODUCTION_GUI_WEB_RENDERER_PARITY_SURFACE_MANIFEST_RESUME=1`,
  `PRODUCTION_GUI_WEB_RENDERER_PARITY_SURFACE_TIMEOUT_SECS`, and
  `PRODUCTION_GUI_WEB_RENDERER_PARITY_TAURI_CAPTURE_WAIT_STEPS`. For focused
  repair runs, set `PRODUCTION_GUI_WEB_RENDERER_PARITY_SURFACE_CASE_FILTER`
  (or the nested `TAURI_CHROME_LAYOUT_CASE_FILTER`) to a whitespace-separated
  case list, such as `css_box_matrix text_raster_track`; unset the filter for
  release evidence. macOS Tauri capture uses the in-repo
  `tools/tauri-live-bitmap/capture_snapshot.swift` WKWebView snapshot backend,
  requires `swift,node`, emits
  `tauri_chrome_simple_web_layout_manifest_tauri_capture_backend=macos-wkwebview-snapshot`,
  and validates ARGB artifacts with producer `macos-wkwebview-snapshot`.
  Its converter uses the deterministic `wkwebview` expected-profile overlay for
  known fixture-scoped WebKit raster differences such as 1-LSB CSS box color
  shifts and native form-control antialias pixels. This remains exact
  pairwise-ARGB comparison evidence: the proof must still emit
  `mismatch_count=0` and `blur_or_tolerance_used=false`.
  Linux Tauri capture remains an Xvfb/X11 path; the host must provide the
  GTK/WebKit development stack plus `openbox`, `xvfb-run`,
  `dbus-run-session`, `xdotool`, ImageMagick `import`/`convert`, and `node`
  before the wrapper can produce live Tauri ARGB evidence. The Linux Tauri
  layout bitmap wrapper launches the shell with
  `SIMPLE_TAURI_CAPTURE_WINDOW=1` and capture dimensions so the evidence window
  is undecorated, fixed-size, and comparable to the expected ARGB fixture.
  The same source env must now include Electron/Chromium interaction evidence
  from `scripts/check/check-wm-browser-event-routing-evidence.shs`. The
  wrapper forwards it as `production_gui_web_renderer_parity_event_routing_*`,
  and the non-launching gate requires `status=pass`, `ready=true`,
  `wm_found=true`, counts of at least one for focus, move, maximize,
  title-command, text-input, pointer-down, and pointer-up, plus
  `blur_or_tolerance_used=false`. Saved render/capture evidence without these
  event-routing keys is no longer a production GUI/web pass claim.

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
summary from `build/renderdoc/chrome-implicit-layer-default-autocapture/html/evidence.env` by default.
That summary is produced with:

```sh
RDOC_EXTERNAL_RUN_CAPTURE=1 \
  BUILD_DIR=build/renderdoc/chrome-implicit-layer-default-autocapture \
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
RDOC_OUTPUT_DIR=build/renderdoc/electron-implicit-layer-default-autocapture \
  scripts/tool/renderdoc-evidence.shs capture-electron-html

RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/renderdoc/electron-implicit-layer-default-autocapture/electron-html/evidence.env \
  sh scripts/check/check-renderdoc-electron-html-gate.shs
```

The gate passes only when the source evidence contains:

- `rdoc_backend=electron`
- `rdoc_capture_status=pass`
- `rdoc_capture_magic=RDOC`
- `rdoc_chromium_requested_api=vulkan`
- `rdoc_chromium_requested_angle=vulkan`
- `rdoc_electron_launch_exit_code`
- `rdoc_electron_launch_timed_out`
- an existing `.rdc` path in `rdoc_capture_file`

Missing RenderDoc, missing Electron capture output, non-Electron backend
evidence, or non-Vulkan Chromium request metadata all keep the gate out of
`pass`.
If retained evidence lacks the launch exit-code or timeout rows and is older
than `scripts/lib/renderdoc-evidence-common.shs`, the gate emits
`rdoc_electron_html_gate_source_contract_status=stale` and a
`stale-source-missing-launch-*` reason. Refresh the Electron capture before
debugging the host in that case; the aggregate cache key includes the Electron
gate script and shared capture helper so contract changes invalidate cached
gate output.

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
`dlsym`, `vkGetDeviceProcAddr`, `vkGetInstanceProcAddr`,
`vkEnumeratePhysicalDevices`, selected physical-device query calls,
`vkQueueSubmit`, `vkQueueSubmit2`, `vkQueueSubmit2KHR`, and `vkQueuePresentKHR`
to call
RenderDoc's in-application capture API from inside the GPU process. Current
Linux evidence records `rdoc_autocapture_loaded=1` and confirms Chromium asks
`dlsym` for `vkGetInstanceProcAddr`, enumerates physical devices, and reads
device properties, including `vk_get_physical_device_properties2` on current
Chrome evidence. The shim logs `rdoc_autocapture_physical_device_properties2`
and the requested `rdoc_autocapture_physical_device_properties2_pnext` chain;
on the current Linux host Chromium asks for physical-device ID plus driver
properties, RenderDoc reports the same NVIDIA driver identity and device UUIDs
as the clear-layer path, and `vkEnumerateInstanceVersion` returns the same
version in both paths. The layer-active path still lowers the physical-device
`apiVersion` reported through properties2 and stops before the later
WSI-enabled `vkCreateInstance`, queue-family, device-extension, and
logical-device queries. If the summary shows
`vk_get_physical_device_queue_family:0`,
`vk_get_physical_device_queue_family2:0`,
`vk_enum_device_extension:0`, and `vk_create_device:0`, Chromium stopped before
logical device selection in the hooked GPU process. If the same run with
`RDOC_GPU_LAUNCHER_CLEAR_RENDERDOC_LAYER=1` reaches `vk_create_device`,
submit, and present, the local blocker is the RenderDoc Vulkan layer path, not
Chromium's Vulkan backing or the shim. Use
`RDOC_GPU_LAUNCHER_CLEAR_INSTANCE_LAYERS=1` and
`RDOC_GPU_LAUNCHER_CLEAR_RENDERDOC_ENABLE=1` to isolate explicit-layer versus
implicit enablement. If either knob alone still blocks and both together reach
frames, the blocker is layer activation itself. That remains diagnostic
evidence rather than a passing `.rdc` gate. Clearing both activation knobs and
setting `RDOC_GPU_LAUNCHER_NO_DLOPEN_FALLBACK=0` can prove late RenderDoc API
loading without startup crashes, but `rdoc_autocapture_end=... ok=0` still
means no browser `.rdc` was captured; this has been observed on both Chrome and
Electron Chromium. `RDOC_GPU_LAUNCHER_START_ON_DLSYM=1` is an opt-in
diagnostic that starts capture as soon as `vkGetInstanceProcAddr` is resolved;
on this host it crashes Chrome's GPU process with exit code 139 and still does
not produce `.rdc`, so keep it off for canonical evidence runs.

Every loaded autocapture shim now appends a final summary row to the launcher
log:

```text
rdoc_autocapture_summary=status:<state> api:<0|1> started:<0|1> finished:<0|1> start_source:<hook> end_source:<hook> submit:<n> present:<n> egl_swap:<n> ...
```

Chromium may launch multiple short-lived GPU processes into one launcher log.
The shared evidence helper scores all `rdoc_autocapture_summary` rows and emits
the most informative one, using line order only to break equal-score ties, so a
later `status:not-started api:0` restart does not hide an earlier
`api:1 started:1 finished:1` diagnostic attempt.

Use that row only for blocker triage. `status:not-started api:0` means the shim
loaded but RenderDoc API discovery did not complete. `api:1 started:0` means the
RenderDoc API was reachable but no configured submit/present/EGL hook started a
capture. `started:1 finished:0` records a start hook without a matching end
hook before process exit. `status:ended` still is not a browser pass unless the
normal evidence wrapper also records a `.rdc` with `RDOC` magic.

The host-independent contract is covered by:

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/renderdoc_vulkan_autocapture_spec.spl --native
```

For the Simple-side GUI widget RenderDoc proof, capture the generated widget
fixture with the dedicated Simple program:

```sh
RDOC_OUTPUT_DIR=build/renderdoc/widget-probe-small \
RDOC_SIMPLE_BIN="$PWD/src/compiler_rust/target/release/simple" \
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
the generated fixture path, positive `rdoc_simple_widget_html_bytes`, Vulkan
runtime metadata, and `.rdc` `RDOC` magic.
The widget goal passes only when the Simple widget capture and Electron
Chromium/Vulkan widget evidence both pass, all 43 widget feature witnesses are
covered, and `gui_widget_renderdoc_goal_blocked_gate_count=0`.

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
- `tools/electron-live-bitmap/renderdoc_display_html.js` is the default
  RenderDoc Electron runner. It avoids `capturePage()`, loads the fixture as a
  data URL by default, and holds a visible page open while the GPU-process shim
  triggers RenderDoc. On Linux with the repo-local Vulkan-only RenderDoc tree
  and a display, `capture-electron-html` defaults to GPU autocapture and emits
  `electron_gpu_capture.rdc` with `RDOC` magic; see
  `build/renderdoc/electron-vulkan-only-default-display-gpu-20260702`.
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
  Current EGL-return diagnostics further narrow the layer-present path. With
  the stock GL/GLES/EGL-enabled RenderDoc build, Chrome and Electron enter
  `eglInitialize` and report
  `rdoc_gpu_autocapture_egl_initialize_return_count=0` before `.rdc` remains
  missing. The complementary `RDOC_GPU_LAUNCHER_CLEAR_RENDERDOC_LAYER=1` probe
  crashes both browser GPU children with `exit_code=139` before useful wrapper
  EGL/Vulkan telemetry, and `RDOC_GPU_LAUNCHER_LAYER_ONLY=1` without the preload
  shim still produces no `.rdc`. The focused evidence is recorded in
  `doc/09_report/renderdoc_browser_gpu_layer_isolation_2026-06-29.md`.
  `RENDERDOC_HOOK_EGL=0` is also ineffective on this Linux host: Chrome and
  Electron still enter `eglInitialize`, report
  `rdoc_gpu_autocapture_egl_initialize_return_count=0`, and produce no `.rdc`.
  Per ANGLE's upstream debugging guide, the viable Linux route is a RenderDoc
  build without GL/GLES support. The repo-local Vulkan-only RenderDoc build path
  now exists, is selected by default on Linux when present, and produces a valid
  Chrome `.rdc` in `build/renderdoc/chrome-vulkan-only-egl-direct-20260702`.
  The autocapture shim also logs direct EGL wrapper returns such as
  `rdoc_autocapture_egl_get_platform_display`,
  `rdoc_autocapture_egl_initialize`, and
  `rdoc_autocapture_egl_make_current` to distinguish EGL entry from EGL return.
  Electron still fails before that GPU-launcher telemetry is available.
- The Chrome target-control diagnostic can use a headless C++ client when the
  active RenderDoc tree has `librenderdoc.so` but no `qrenderdoc`, which is the
  case for the repo-local Vulkan-only build. The wrapper auto-builds
  `scripts/tool/renderdoc-target-control-client.cpp` against
  `build/tools/renderdoc-src` when needed, connects directly to RenderDoc's
  target-control server, and sends `TriggerCapture(1)` without qrenderdoc UI
  Python. It still wraps qrenderdoc in an outer timeout when qrenderdoc is the
  selected client. The diagnostic records
  `rdoc_chrome_target_control_gpu_env_has_layer`,
  `rdoc_chrome_target_control_gpu_maps_has_renderdoc`,
  `rdoc_chrome_target_control_gpu_maps_has_vulkan`,
  `rdoc_chrome_target_control_renderdoc_debug_log_vulkan_instance_status`,
  `rdoc_chrome_target_control_target_ident_count`,
  `rdoc_chrome_target_control_target_api`,
  `rdoc_chrome_target_control_target_api_message_count`,
  `rdoc_chrome_target_control_target_window_message_count`,
  `rdoc_chrome_target_control_target_message_count`, and
  `rdoc_chrome_target_control_target_noop_count`. Current Vulkan-only evidence
  connects to the GPU process target, but RenderDoc's log never reaches
  `Initialised capture layer in Vulkan instance`, so
  `rdoc_chrome_target_control_renderdoc_debug_log_vulkan_instance_status=missing`.
  A 12s pre-trigger API wait reports no API-use messages and no
  capturable-window messages; target API remains empty and every post-trigger
  message is `Noop`, so no `.rdc` is produced. If Chrome does not create a GPU
  process, the script fails closed with
  `rdoc_chrome_target_control_reason=no-gpu-process` before triggering capture
  on an unrelated target:

```sh
RDOC_HOME=build/tools/renderdoc-linux-vulkan-only \
RDOC_TARGET_CONTROL_WAIT_API_SECS=12 \
  sh scripts/check/check-renderdoc-chrome-target-control.shs
```
- Running Electron with the ARGB capture helper under RenderDoc can still time
  out before ARGB output. The canonical Electron RenderDoc gate accepts the
  display holder for `.rdc` proof; ARGB/pixel proof remains covered by the
  separate GUI/Web direct-run evidence.
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
