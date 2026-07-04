# Bug: GUI/web/2D Vulkan RenderDoc blockers remain

Status: open
Date: 2026-06-23
Area: GUI/web/2D Vulkan, RenderDoc capture gates

## Symptom

The aggregate GUI audit must stay incomplete when:

- `gui_web_2d_vulkan_renderdoc_blocker_status=blocked`
- `gui_web_2d_vulkan_renderdoc_blocker_reason` names the current missing
  command, source evidence, browser Vulkan, RenderDoc, or pairwise ARGB diff
  gate
- `gui_web_2d_vulkan_renderdoc_blocker_gate_count` is nonzero
- `gui_web_2d_vulkan_renderdoc_blocker_gates` lists missing or unsupported
  Simple, Electron, Chrome, or macOS RenderDoc capture gates

Artifact presence alone is not enough. Required `.rdc` files must pass the
RenderDoc gate checks and have `RDOC` magic.

## Required Evidence

Completion requires the aggregate audit to prove:

- `gui_web_2d_vulkan_renderdoc_blocker_status=pass`
- `gui_web_2d_vulkan_renderdoc_blocker_reason=pass`
- `gui_web_2d_vulkan_renderdoc_blocker_gate_count=0`
- Simple Vulkan Engine2D RenderDoc evidence passes
- Electron Chromium/Vulkan and Chrome Vulkan `.rdc` evidence passes
- macOS hosts use the supported Simple RenderDoc debug path or record the
  platform blocker without claiming completion

Use the canonical capture entrypoints:

- `scripts/tool/renderdoc-evidence.shs capture-simple`
- `scripts/tool/renderdoc-evidence.shs capture-html`
- `scripts/tool/renderdoc-evidence.shs capture-electron-html`

Aggregate evidence may report compatibility check commands such as
`scripts/check/check-renderdoc-external-host-capture.shs`; use the
`renderdoc-evidence.shs` entrypoints above for fresh capture work.

## Current Linux Simple Capture State

Current routing note, 2026-06-27: the passing 2026-06-26 Simple capture rows
below are historical evidence from a host/session where RenderDoc resolved.
Fresh host discovery for the active Linux lane is recorded in
`doc/09_report/gui_web_2d_linux_renderdoc_host_blocker_2026-06-27.md` and
currently reports `missing-renderdoccmd-in-search-paths`. Do not reuse the
historical `qrenderdoc` or `renderdoccmd` availability as current proof; rerun
the canonical capture entrypoints on a prepared host with `renderdoccmd`
available on `PATH` or under `RDOC_HOME`.

2026-06-26 focused passing evidence:
`build/gui-web-2d-vulkan-env-renderdoc-simple-explicit-layer-owner-env/renderdoc/simple/evidence.env`.

Resolved:

- RenderDoc command discovery resolves `/usr/local/bin/renderdoccmd` symlinks to
  the real `/opt/renderdoc` home.
- Simple uses the Rust interpreter at `src/compiler_rust/target/release/simple`
  so `rt_renderdoc_*` externs resolve.
- Simple Vulkan readback passes on Intel(R) Graphics (RPL-P).
- The Simple capture now passes RenderDoc's Vulkan device pointer
  (`*((void **)VkInstance)`), not `VkDevice`; evidence shows a nonzero
  `rdoc_simple_renderdoc_device`.
- The helper creates a per-run RenderDoc Vulkan layer manifest with
  `library_path=/opt/renderdoc/lib/librenderdoc.so` and forces
  `VK_INSTANCE_LAYERS=VK_LAYER_RENDERDOC_Capture`.
- `rdoc_simple_renderdoc_capturing_after_start=1`
- `rdoc_simple_renderdoc_end=1`
- `rdoc_simple_renderdoc_num_captures=1`
- `rdoc_capture_status=pass`
- `rdoc_capture_magic=RDOC`

Still blocked:

- Chrome Vulkan `.rdc` evidence with `RDOC` magic.
- Electron Chromium/Vulkan `.rdc` evidence with `RDOC` magic and nonblank ARGB.

Current 2026-06-26 browser capture findings:

- Browser Vulkan backing itself now passes:
  `build/gui-web-2d-vulkan-env-browser-backing-electron42/evidence.env`
  reports Electron `vulkan=enabled_on` and Chrome `ANGLE_VULKAN`.
- Chrome RenderDoc with child-process hooking on the real Xwayland display
  still crashes the Chromium GPU process repeatedly with `exit_code=139`;
  evidence:
  `build/renderdoc/chrome-display-helper/html/evidence.env` and
  `build/renderdoc/chrome-real-xwayland-hook/renderdoc-html.log`.
- Chrome under Xvfb without child-process hooking no longer hits the same GPU
  crash, but Vulkan presentation fails because Xvfb has no DRI3 support:
  `build/renderdoc/chrome-no-child-hook-x11/renderdoc-html.log`.
- Chrome single-process is not acceptable because Chromium reports
  `Vulkan not supported with in process gpu`; evidence:
  `build/renderdoc/chrome-single-process-real-xwayland/renderdoc-html.log`.
- Chrome GPU-process-only RenderDoc launch is available through
  `RDOC_CHROME_GPU_LAUNCHER=1`, but it still does not produce `.rdc`: the GPU
  process repeatedly starts through `scripts/tool/renderdoc-gpu-launcher.shs`
  and exits. Evidence:
  `build/renderdoc/chrome-gpu-launcher-helper/html/evidence.env` and
  `build/renderdoc/chrome-gpu-launcher-helper/html/gpu-launcher.log`.
- Chrome GPU-process autocapture through
  `RDOC_CHROME_GPU_AUTOCAPTURE=1` preloads
  `scripts/tool/renderdoc-vulkan-autocapture.c` into the GPU process, but the
  shim only records diagnostic state; Chromium does not reach the wrapped
  Vulkan queue submit/present hooks before timeout/failure, so no `.rdc` is
  produced. Fresh runs should inspect `rdoc_autocapture_summary=...` in
  `gpu-launcher.log` to distinguish API discovery, start-hook, end-hook, and
  counter state. Evidence:
  `build/renderdoc/chrome-gpu-autocapture-wrap/html/evidence.env` and
  `build/renderdoc/chrome-gpu-autocapture-wrap/html/gpu-launcher.log`.
- A follow-up Chrome GPU autocapture probe added wrappers for
  `vkQueueSubmit2`/`vkQueueSubmit2KHR`; evidence still showed no submit or
  present hook before `missing-rdc`:
  `build/renderdoc/chrome-gpu-autocapture-submit2/html/evidence.env`.
- A follow-up dlsym probe confirmed the Chromium GPU process resolves
  `vkGetInstanceProcAddr` through `dlsym`, but starting capture at that point
  (`RDOC_GPU_LAUNCHER_START_ON_DLSYM=1`) crashes the GPU process with
  `exit_code=139` and still produces no `.rdc`. Evidence:
  `build/renderdoc/chrome-gpu-autocapture-dlsym-start/html/evidence.env` and
  `build/renderdoc/chrome-gpu-autocapture-dlsym-start/html/gpu-launcher.log`.
- Chrome headless/in-process does not produce a presentable frame or `.rdc`,
  so it is not acceptable RenderDoc evidence.
- Electron 42 with `--ozone-platform=x11` renders Vulkan-backed ARGB outside
  RenderDoc, but under `renderdoccmd capture` on the real display it exits with
  `SIGTRAP` before ARGB or `.rdc` output. Earlier `xvfb-run` attempts also
  showed `ERR_FAILED` before the document-write fallback; after the fallback,
  both Xvfb and real-display launches trap. Evidence:
  `build/renderdoc/electron-display-helper/electron-html/evidence.env`,
  `build/renderdoc/electron42-real-xwayland-hook/renderdoc-electron-html.log`,
  and
  `build/renderdoc/electron42-explicit-layer-document-write/electron-html/evidence.env`.
- Electron GPU-process-only RenderDoc launch is available through
  `RDOC_ELECTRON_GPU_LAUNCHER=1`, but it fails before ARGB or `.rdc` with
  `UnknownVizError`. Evidence:
  `build/renderdoc/electron-gpu-launcher-helper/electron-html/evidence.env` and
  `build/renderdoc/electron-gpu-launcher-helper/electron-html/gpu-launcher.log`.
- Electron GPU-process autocapture through
  `RDOC_ELECTRON_GPU_AUTOCAPTURE=1` also loads the shim but does not reach the
  wrapped Vulkan queue hooks before timeout, so it produces neither ARGB nor
  `.rdc`. Evidence:
  `build/renderdoc/electron-gpu-autocapture-wrap/electron-html/evidence.env`
  and
  `build/renderdoc/electron-gpu-autocapture-wrap/electron-html/gpu-launcher.log`.

2026-06-26 canonical rerun:
- Simple Vulkan Engine2D evidence passes with `.rdc` magic `RDOC`:
  `build/renderdoc/canonical-probe/simple/evidence.env`.
- Chrome-on-Vulkan external host evidence reaches the generated HTML fixture
  but still fails `missing-rdc` after repeated Chromium GPU process
  `exit_code=139`: `build/renderdoc/html-external-host-capture/evidence.env`.
- Electron Chromium/Vulkan evidence uses the generated HTML fixture and Vulkan
  launch flags, but the GPU process exits `139` under RenderDoc and no ARGB or
  `.rdc` file is produced:
  `build/renderdoc/canonical-probe/electron-html/evidence.env`.

2026-06-29 gate/reporting hardening:
- Browser Vulkan backing itself passes in the current aggregate through
  `build/gui-web-2d-vulkan-env-browser-backing/evidence.env`; this is not
  RenderDoc `.rdc` proof.
- Chrome external-host capture now preserves the raw capture reason
  `missing-rdc`, but promotes the actionable gate reason to
  `chromium-gpu-process-crashed-under-renderdoc` when the capture log records
  Chromium GPU process exits. Current evidence reports 9 exits with code `139`:
  `build/renderdoc/chrome-display-helper/evidence.env` and
  `doc/09_report/renderdoc_external_host_capture_2026-06-29.md`.
- The aggregate GUI/web/2D RenderDoc blocker gates now identify both browser
  failures by the concrete GPU-process crash class:
  `electron-renderdoc-gate-fail-chromium-gpu-process-crashed-under-renderdoc`
  and
  `chrome-renderdoc-gate-fail-chromium-gpu-process-crashed-under-renderdoc`.
  Evidence:
  `doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-29.md`.
- Raw browser capture envs and the Linux render-log comparison now also expose
  the GPU-process exit counts and codes, so missing `.rdc` remains visible as
  the artifact failure while the crash class stays machine-readable. Current
  aggregate values: Chrome `9` exits with code `139`, Electron `6` exits with
  code `139`.
- The Chrome X11 layer/hotkey diagnostic now has a layer-only GPU launcher mode
  (`RDOC_CHROME_HOTKEY_GPU_LAUNCHER=1`) that forces the Chromium GPU child
  through `scripts/tool/renderdoc-gpu-launcher.shs` without wrapping it in
  `renderdoccmd capture`. Current evidence shows the launcher is invoked with
  `renderdoc_gpu_launcher_layer_only=1`, and the GPU process maps both
  `librenderdoc` and `libvulkan` without crashing. A follow-up provenance run
  proves the launcher exec PID and inspected GPU PID are the same process, and
  the launcher exports `RENDERDOC_CAPFILE` plus `RENDERDOC_DEBUG_LOG_FILE`
  before `exec`. The RenderDoc debug log is written by that GPU process and
  records RenderDoc v1.44 loading into Chrome plus Vulkan hook registration, so
  the layer is active. The X11 app window that receives the generated hotkeys is
  owned by the browser process, not the GPU process where RenderDoc is loaded,
  so the hotkey route cannot reach the active RenderDoc layer; no `.rdc` is
  produced. Current reason:
  `hotkey-window-owned-by-browser-not-renderdoc-gpu-process`. Evidence:
  `doc/09_report/renderdoc_chrome_x11_layer_hotkey_gpu_launcher_2026-06-29.md`.
- The minimal delay-trigger GPU-child shim now supports
  `RDOC_GPU_LAUNCHER_DELAY_TRIGGER_MODE=trigger`, which calls RenderDoc's
  `TriggerCapture()` without exporting EGL or Vulkan wrapper symbols. Current
  Chrome and Electron probes both load the shim, resolve `RENDERDOC_GetAPI`
  from the already-loaded Vulkan-only `librenderdoc.so`, set the capfile
  template, and call `TriggerCapture()` once, but
  `rdoc_gpu_delay_trigger_num_captures_after=0`,
  `rdoc_gpu_delay_trigger_is_capturing_after_trigger=0`, and no `RDOC` artifact
  is produced. Evidence:
  `build/renderdoc/chrome-gpu-triggercapture-vulkan-only/html/evidence.env`,
  `build/renderdoc/electron-gpu-triggercapture-vulkan-only/electron-html/evidence.env`,
  and
  `doc/09_report/renderdoc_browser_delay_trigger_vulkan_only_2026-06-29.md`.
- A targeted-device variant of the same shim attempts to intercept
  `vkCreateInstance` and call `StartFrameCapture(device,NULL)` using
  `RENDERDOC_DEVICEPOINTER_FROM_VKINSTANCE`, but both Chrome and Electron
  report `rdoc_gpu_delay_trigger_vk_create_instance_count=0`,
  `rdoc_gpu_delay_trigger_target_device=(nil)`, and `missing-rdc`. Evidence:
  `build/renderdoc/chrome-gpu-delay-device-target-vulkan-only/html/evidence.env`
  and
  `build/renderdoc/electron-gpu-delay-device-target-vulkan-only/electron-html/evidence.env`.
- The Chrome target-control lane now has a headless C++ client for the
  Vulkan-only RenderDoc build, so it no longer depends on `qrenderdoc`
  availability. Current evidence auto-builds the client, connects to the
  Chromium GPU process target-control server, selects the GPU PID, and sends
  `TriggerCapture(1)`. With a 12s pre-trigger wait, the target reports
  `rdoc_chrome_target_control_renderdoc_debug_log_vulkan_instance_status=missing`,
  `target_api=`, `rdoc_chrome_target_control_target_api_message_count=0`,
  `rdoc_chrome_target_control_target_window_message_count=0`, and then returns
  only Noop messages after trigger
  (`rdoc_chrome_target_control_target_message_count=3875`,
  `rdoc_chrome_target_control_target_noop_count=3875`), so no `NewCapture`
  message or `.rdc` is produced. Current reason:
  `target-control-no-api-use-renderdoc-layer-not-in-vulkan-instance`. Evidence:
  `build/renderdoc/chrome-target-control-vulkan-instance-status/evidence.env`
  and `doc/09_report/renderdoc_chrome_target_control_2026-06-29.md`.

2026-06-26 follow-up diagnostics:
- `renderdoccmd inject --PID=<chrome-gpu-pid>` is not a Linux workaround.
  RenderDoc reports: injection into already-running processes is not supported
  on non-Windows systems. Evidence:
  `build/renderdoc/chrome-late-inject-probe/inject.log`.
- Chrome with only `VK_LAYER_RENDERDOC_Capture`, `ENABLE_VULKAN_RENDERDOC_CAPTURE=1`,
  and `RENDERDOC_CAPFILE` keeps the Vulkan GPU process alive, unlike
  `renderdoccmd capture --opt-hook-children`, but the automated F12 hotkey
  probe did not create `.rdc`. Evidence:
  `build/renderdoc/chrome-layer-hotkey-probe/rdc.list`.
- A repeatable X11 app-window hotkey probe now exists at
  `scripts/check/check-renderdoc-chrome-x11-layer-hotkey.shs`. It opens the
  generated fixture in Chrome app mode with `--ozone-platform=x11`, records the
  fixture window id and live Vulkan GPU process, sends F12/Print/F12, and still
  reports `missing-rdc` on this host. Evidence:
  `build/renderdoc/chrome-x11-layer-hotkey/evidence.env`.
- A source-derived `RENDERDOC_CAPOPTS` run with `refAllResources` and
  `captureAllCmdLists` enabled also reports `missing-rdc`; this rules out the
  earlier hotkey probe failing solely because capture options were absent.
  Evidence:
  `build/renderdoc/chrome-x11-layer-hotkey-capopts/evidence.env`.
- Electron with the RenderDoc Vulkan layer only still did not complete the ARGB
  capture script before timeout and produced no `.rdc`. Evidence:
  `build/renderdoc/electron-layer-only-probe/electron.log`.
- Chrome GPU-process delayed autocapture now starts a background trigger thread
  after GPU-process launch. Without preloading `librenderdoc.so`, the GPU
  process reaches the delayed trigger but cannot obtain a usable RenderDoc API
  and still produces no `.rdc`:
  `build/renderdoc/chrome-gpu-autocapture-delay-defaultsym/html/gpu-launcher.log`.
- Preloading `librenderdoc.so` into the Chromium GPU process gives the shim a
  RenderDoc library earlier but reintroduces repeated GPU-process
  `exit_code=139`, so it is not a passing path:
  `build/renderdoc/chrome-gpu-autocapture-delay-preload/html/gpu-launcher.log`.
- Electron GPU-process delayed autocapture also starts the delayed trigger
  thread, but still times out before ARGB output or `.rdc` evidence:
  `build/renderdoc/electron-gpu-autocapture-delay/electron-html/gpu-launcher.log`.

2026-06-26 deeper Chrome layer/control diagnostics:
- The generated HTML fixture now includes a small CSS/rAF pulse and WebGL draw
  loop so browser captures have continuous presentation pressure and explicit
  ANGLE work while preserving the widget/HTML/CSS coverage surface.
- The X11 layer-only Chrome probe now records GPU-process maps. Evidence from
  `build/renderdoc/chrome-x11-layer-hotkey-maps/evidence.env` and later
  reruns shows `librenderdoc` and `libvulkan` are both mapped in the Chromium
  GPU process, but the probe still reports `missing-rdc`.
- Holding global F11/F12/Print keys for one second each did not trigger a
  capture. Evidence:
  `build/renderdoc/chrome-x11-layer-hotkey-globalkey/evidence.env`.
- `qrenderdoc --python` and `qrenderdoc --ui-python` do not execute even a
  smoke script within the local timeout on this host; `QT_QPA_PLATFORM=xcb`
  also times out and offscreen/minimal platforms are unavailable. Evidence:
  `build/renderdoc/qrenderdoc-python-smoke/`,
  `build/renderdoc/qrenderdoc-ui-python-smoke/`,
  `build/renderdoc/qrenderdoc-xcb-smoke/`.
- The Chromium GPU-process autocapture shim now has a loader-lock-free ELF
  symbol lookup for `RENDERDOC_GetAPI`. This avoids the deadlocks seen in
  `dlsym(RTLD_DEFAULT, ...)` and `dlopen(... RTLD_NOLOAD)`, and reaches
  `rdoc_autocapture_api=ready`. Evidence:
  `build/renderdoc/chrome-gpu-autocapture-elf-api-fixed/html/gpu-launcher.log`.
- Even after the API is reachable, `StartFrameCapture(NULL,NULL)` ends with
  `ok=0`, and `TriggerCapture()` does not create `.rdc` on this host. Evidence:
  `build/renderdoc/chrome-gpu-autocapture-elf-wrap-webgl/html/gpu-launcher.log`
  and
  `build/renderdoc/chrome-gpu-autocapture-trigger-webgl/html/gpu-launcher.log`.

2026-06-26 deeper Electron stage diagnostics:
- The Electron GPU-process autocapture path reaches the same loader-lock-free
  RenderDoc API state as Chrome: `rdoc_autocapture_elf=symbol-found` and
  `rdoc_autocapture_api=ready`, but `TriggerCapture()` still does not emit an
  `.rdc`. Evidence:
  `build/renderdoc/electron-gpu-autocapture-elf-trigger-offscreen-failfast/electron-html/gpu-launcher.log`.
- Under the injected GPU process, Electron `loadFile(...)` and `loadURL(data:)`
  can time out. With `ELECTRON_CAPTURE_CONTINUE_AFTER_LOAD_TIMEOUT=1`, the
  capture script can still reach media setup, DOM audit, and geometry collection.
  Evidence:
  `build/renderdoc/electron-gpu-autocapture-elf-trigger-offscreen-failfast/electron-html/electron-stage.log`.
- `BrowserWindow.capturePage(...)` hangs in the same injected path. Offscreen
  paint mode now fails fast instead of falling through to `capturePage`; the
  latest diagnostic reached `missing-offscreen-paint`, so the current Electron
  blocker is both missing `.rdc` and missing a usable ARGB bitmap under
  RenderDoc injection.

2026-06-26 deeper Chromium proc-path diagnostics:
- The local RenderDoc install initially reported `vulkanlayer --explain` as
  unregistered. Running `/opt/renderdoc/bin/renderdoccmd vulkanlayer --register
  --user` fixed user-level layer registration, but did not close the browser
  gates: Chrome and Electron still report `missing-rdc`, and direct
  `renderdoccmd capture` continues to restart Chromium GPU processes with
  `exit_code=139`. Evidence:
  `build/renderdoc/chrome-after-user-layer-register/html/evidence.env` and
  `build/renderdoc/electron-after-user-layer-register/electron-html/evidence.env`.
- The GPU-process launcher now exports `RENDERDOC_CAPFILE` and optional
  `RENDERDOC_CAPOPTS` before the RenderDoc Vulkan layer initializes, not only
  the later in-application `SetCaptureFilePathTemplate(...)` path. This removes
  an early layer-configuration ambiguity, but Chrome still reports `missing-rdc`.
  Evidence:
  `build/renderdoc/chrome-gpu-autocapture-x11-capfile-capopts/html/gpu-launcher.log`.
- The Chrome GPU-process RenderDoc path now forces `--ozone-platform=x11` to
  match the Vulkan browser-backing path. The GPU process receives X11 and
  `--use-angle=vulkan`, but still records no `.rdc`:
  `build/renderdoc/chrome-gpu-autocapture-x11-capfile-capopts/html/evidence.env`.
- The autocapture shim can trace capped `dlsym`, `eglGetProcAddress`,
  `vkGetInstanceProcAddr`, `vkGetDeviceProcAddr`, queue submit/present,
  `eglSwapBuffers`, and ANGLE Vulkan queue lock/unlock paths. Current Chrome
  app-mode evidence shows the GPU process looks up EGL and ANGLE Vulkan symbols
  including `EGL_LockVulkanQueueANGLE`, `EGL_UnlockVulkanQueueANGLE`, and
  `vkGetInstanceProcAddr`, but the wrapped submit/present/swap/lock calls do
  not execute in that GPU process before timeout. Evidence:
  `build/renderdoc/chrome-gpu-autocapture-angle-vk-lock/html/gpu-launcher.log`.
- The Chrome target-control probe now wraps `qrenderdoc --ui-python` with an
  outer timeout so a UI Python startup failure cannot hang evidence collection.
  After layer registration it still produced no target-control Python evidence:
  `build/renderdoc/chrome-target-control-timeout-bounded/evidence.env`.
- 2026-06-29 target-control rerun aligns the Chrome launch flags with the
  canonical Vulkan browser path and records RenderDoc debug-log proof. The
  Chrome GPU process loads RenderDoc and registers Vulkan hooks, but
  `qrenderdoc --ui-python` exits by timeout (`rc=124`) with an empty log and no
  `target-control.env`, so no `.rdc` is produced. Current reason:
  `qrenderdoc-ui-python-timeout-without-target-evidence`. Evidence:
  `doc/09_report/renderdoc_chrome_target_control_2026-06-29.md`.
- 2026-06-29 Chrome GPU-process autocapture evidence now emits structured
  `rdoc_gpu_autocapture_*` fields from `gpu-launcher.log`. Current Chrome
  app-mode evidence with `RDOC_AUTOCAPTURE_SUMMARY_INTERVAL_MS=2000` reports
  `rdoc_gpu_autocapture_status=not-started`, `api=0`, and zero
  submit/present/EGL swap/ANGLE queue counters after tracing 160 proc names.
  This proves the shim is alive but none of the currently wrapped frame trigger
  calls execute before timeout, so no `.rdc` is produced. Evidence:
  `build/renderdoc/chrome-gpu-autocapture-current/html/evidence.env`.
- Adding `--no-zygote` to the Chromium launch contract did not fix the direct
  Chrome RenderDoc capture; Chrome still restarts the GPU process with
  `exit_code=139` and produces no `.rdc`. Evidence:
  `build/renderdoc/chrome-no-zygote-renderdoc-display/html/evidence.env`.
- The Chrome wrapper previously printed broadened Vulkan flags as metadata while
  some launch branches still used older hardcoded flags. The launch branches now
  route through `rdoc_chrome_vulkan_flags`. A rerun with the actual broadened
  flags still fails with Chromium GPU-process `exit_code=139` and no `.rdc`:
  `build/renderdoc/chrome-broad-vulkan-flags-renderdoc-fixed/html/evidence.env`.
- The older local `/home/yoon/electron-vulkan` recipe is no longer a passing
  route on this host: current Electron reports `Vulkan not supported with in
  process gpu`, and the repo Electron in-process-GPU RenderDoc run segfaults
  before `.rdc` output:
  `build/renderdoc/electron-in-process-gpu-renderdoc/electron-html/evidence.env`.
- Electron GPU-process autocapture with a visible window and data URL reaches
  load/settle/capture stages but still produces no `.rdc`. Without RenderDoc
  preload the shim sees `vkGetInstanceProcAddr` but records missing
  `librenderdoc.so` or stalls in `dlopen`; with explicit preload the Chromium
  GPU process exits `139`. Evidence:
  `build/renderdoc/electron-visible-dataurl-dlsym-trigger-gpu-autocapture/electron-html/gpu-launcher.log`,
  `build/renderdoc/electron-visible-dataurl-dlopen-dlsym-trigger/electron-html/gpu-launcher.log`,
  and
  `build/renderdoc/electron-visible-dataurl-preload-dlsym-trigger/electron-html/evidence.env`.
- A delayed no-dlopen GPU-process trigger now reaches
  `rdoc_autocapture_api=ready` by finding the already-loaded RenderDoc ELF
  symbol and calls `StartFrameCapture`/`EndFrameCapture`, but RenderDoc returns
  `ok=0` with zero submit/present/swap counters and no `.rdc`:
  `build/renderdoc/electron-visible-dataurl-delay-api-retry/electron-html/gpu-launcher.log`.
- The shim now wraps ANGLE scheduling symbols
  `EGL_PrepareSwapBuffersANGLE` and `EGL_WaitUntilWorkScheduledANGLE` in upper-
  and lower-case forms. Chromium resolves these symbols, but the wrappers are
  not called before timeout, so this does not close the `.rdc` gate:
  `build/renderdoc/electron-visible-dataurl-angle-schedule-uppercase-autocapture/electron-html/gpu-launcher.log`.
- A visible display-only Electron runner
  `tools/electron-live-bitmap/renderdoc_display_html.js` avoids `capturePage()`
  and holds a window open for RenderDoc. It still cannot produce `.rdc` on this
  host; both the generated fixture and a tiny animated HTML file time out in
  Electron load while the GPU-process trigger reports no capturable frame:
  `build/renderdoc/electron-display-only-trigger-autocapture/electron-html/gpu-launcher.log`
  and
  `build/renderdoc/electron-display-only-small-trigger/electron-html/gpu-launcher.log`.
- 2026-06-29 Electron GPU-process autocapture now has the same heartbeat
  summary evidence as Chrome. With
  `RDOC_AUTOCAPTURE_SUMMARY_INTERVAL_MS=2000`, the visible-window Electron run
  loads the shim, traces 160 proc-name lookups, records no Chromium GPU-process
  crash, and reports `rdoc_gpu_autocapture_status=not-started`, `api=0`, and
  zero submit/present/EGL swap/ANGLE queue counters before timeout. This proves
  the current failure is not missing shim injection or missing summary emission;
  the wrapped frame trigger calls are not reached in this route. Evidence:
  `build/renderdoc/electron-gpu-autocapture-current/electron-html/evidence.env`
  and `doc/09_report/renderdoc_electron_gpu_autocapture_heartbeat_2026-06-29.md`.
- 2026-06-29 The GPU-process autocapture shim now also records passive EGL
  lifecycle counters for `eglMakeCurrent`, `eglCreateWindowSurface`, and
  `eglCreatePlatformWindowSurface`. Fresh Chrome and Electron probes both
  report shim injection plus 220 proc-name traces, but all new EGL lifecycle
  counters remain zero along with submit/present/swap/ANGLE counters. This
  means the failing route is earlier than the currently wrapped frame and
  surface calls; the next diagnostic should inspect Chromium GPU launcher
  ownership, Vulkan loader/layer dispatch, or RenderDoc layer registration in
  the child process. Evidence:
  `build/renderdoc/chrome-gpu-autocapture-egl-lifecycle/html/evidence.env`,
  `build/renderdoc/electron-gpu-autocapture-egl-lifecycle/electron-html/evidence.env`,
  and `doc/09_report/renderdoc_browser_gpu_autocapture_egl_lifecycle_2026-06-29.md`.
- 2026-06-29 GPU launcher boundary diagnostics now prove the Chrome and
  Electron GPU child commands run with `VK_LAYER_RENDERDOC_Capture`,
  `ENABLE_VULKAN_RENDERDOC_CAPTURE=1`, a RenderDoc capfile, and the autocapture
  shim in `LD_PRELOAD`. In both runs the shim constructor executes
  (`rdoc_gpu_autocapture_loaded_count=1`) and traces 220 proc-name lookups, but
  the capture still remains `not-started` with zero wrapped Vulkan/EGL/ANGLE
  counters and no `.rdc`. This rules out missing GPU launcher invocation,
  missing layer env, missing capfile, missing preload, and missing shim load as
  the current blocker. Evidence:
  `build/renderdoc/chrome-gpu-launcher-boundary-current/html/evidence.env`,
  `build/renderdoc/electron-gpu-launcher-boundary-current/electron-html/evidence.env`,
  and `doc/09_report/renderdoc_browser_gpu_launcher_boundary_2026-06-29.md`.
- 2026-06-29 Vulkan loader-boundary counters now show both Chrome and Electron
  GPU-child routes reach `vkEnumerateInstanceLayerProperties` twice and
  `vkEnumerateInstanceExtensionProperties` once with the RenderDoc layer env
  active, but neither reaches `vkCreateInstance` or `vkCreateDevice` before
  timeout. The shim resolver was hardened to fall back to loaded `libvulkan`
  and `libEGL` symbols so exported diagnostic wrappers do not break ANGLE
  initialization. Evidence:
  `build/renderdoc/chrome-gpu-vulkan-loader-boundary/html/evidence.env`,
  `build/renderdoc/electron-gpu-vulkan-loader-boundary/electron-html/evidence.env`,
  and `doc/09_report/renderdoc_browser_vulkan_loader_boundary_2026-06-29.md`.
- 2026-06-29 Browser evidence now emits structured Chromium ANGLE/EGL
  initialization metadata. The fixed Electron visible-window GPU-launcher route
  reports `rdoc_chromium_angle_status=pass` with zero ANGLE/EGL init errors
  while still reaching only Vulkan layer/extension enumeration and not
  `vkCreateInstance`. The Chrome app-mode GPU-launcher route leaves the main
  Chromium run log empty, so its ANGLE metadata is `missing-log`; GPU-child
  state remains available through `gpu-launcher.log`. Evidence:
  `build/renderdoc/chrome-gpu-angle-init-current/html/evidence.env`,
  `build/renderdoc/electron-gpu-angle-init-current/electron-html/evidence.env`,
  and `doc/09_report/renderdoc_browser_angle_init_metadata_2026-06-29.md`.
- 2026-06-29 The GPU launcher now captures GPU-child stdout/stderr in
  `gpu-launcher.log` and the evidence wrapper emits
  `rdoc_chromium_gpu_launcher_angle_*` fields from that log. Fresh Chrome and
  Electron GPU-launcher probes both report
  `rdoc_chromium_gpu_launcher_angle_status=pass` with zero ANGLE/EGL init
  errors, while still reaching Vulkan layer/extension enumeration but not
  `vkCreateInstance`. This removes the previous Chrome app-mode `missing-log`
  ambiguity for GPU-child diagnostics. Evidence:
  `build/renderdoc/chrome-gpu-launcher-angle-log/html/evidence.env`,
  `build/renderdoc/electron-gpu-launcher-angle-log/electron-html/evidence.env`,
  and `doc/09_report/renderdoc_browser_gpu_launcher_angle_log_2026-06-29.md`.
- 2026-06-29 A diagnostic-only no-layer switch
  `RDOC_GPU_LAUNCHER_CLEAR_RENDERDOC_LAYER=1` clears `VK_INSTANCE_LAYERS` and
  `ENABLE_VULKAN_RENDERDOC_CAPTURE` immediately before GPU-child exec while
  keeping the preload shim. This does not provide a workaround: Chrome reports
  nine GPU-process `exit_code=139` crashes and Electron reports six
  `exit_code=139` crashes, with no `.rdc` in either route. Evidence:
  `build/renderdoc/chrome-gpu-no-renderdoc-layer/html/evidence.env`,
  `build/renderdoc/electron-gpu-no-renderdoc-layer/electron-html/evidence.env`,
  and `doc/09_report/renderdoc_browser_no_layer_isolation_2026-06-29.md`.
- 2026-06-29 Linux aggregate checks now forward the current browser
  GPU-launcher diagnostics. `check-linux-vulkan-render-log-compare.shs` and
  `check-gui-renderdoc-feature-coverage-status.shs` expose Chrome/Electron
  GPU-launcher ANGLE status, no-layer flag, autocapture status, Vulkan
  layer/extension enumeration counts, and `vkCreateInstance`/`vkCreateDevice`
  counts under `linux_vulkan_render_log_compare_renderdoc_*`. The focused
  aggregate still keeps `renderdoc-chrome-rdc` and `renderdoc-electron-rdc`
  blocked with both browser reasons `missing-rdc`. Evidence:
  `build/linux-vulkan-render-log-compare/evidence.env` and
  `doc/09_report/renderdoc_linux_aggregate_browser_fields_2026-06-29.md`.
- 2026-06-29 The autocapture shim now records EGL display/init boundary
  counters. Fresh Chrome and Electron GPU-child probes both report
  `egl_get_platform_display=1`, `egl_initialize=1`, `egl_choose_config=0`,
  `vk_enum_instance_layer=2`, and `vk_create_instance=0`, with GPU-launcher
  ANGLE status still `pass` and no `.rdc`. This narrows the live Linux browser
  blocker to after `eglInitialize` and before EGL config selection / Vulkan
  instance creation. Evidence:
  `build/renderdoc/chrome-gpu-egl-init-boundary/html/evidence.env`,
  `build/renderdoc/electron-gpu-egl-init-boundary/electron-html/evidence.env`,
  and `doc/09_report/renderdoc_browser_egl_init_boundary_2026-06-29.md`.
- 2026-06-29 The EGL boundary diagnostic now records `eglInitialize` return
  status. Fresh Chrome and Electron GPU-child probes both report
  `egl_initialize_count=1`, `egl_initialize_return_count=0`,
  `egl_initialize_success_count=0`, `egl_initialize_fail_count=0`,
  `egl_initialize_last_result=-1`, `egl_initialize_last_error=-1`,
  `egl_choose_config=0`, and `vk_create_instance=0`. This proves both browser
  routes enter `eglInitialize` under the RenderDoc GPU-child shim and do not
  return from that call before timing out without `.rdc`. Evidence:
  `build/renderdoc/chrome-gpu-egl-init-return/html/evidence.env`,
  `build/renderdoc/electron-gpu-egl-init-return/electron-html/evidence.env`,
  `build/linux-vulkan-render-log-compare/evidence.env`, and
  `doc/09_report/renderdoc_browser_egl_initialize_return_2026-06-29.md`.
- 2026-06-29 Existing GPU-launcher isolation switches now classify three
  browser failure modes on Linux. With RenderDoc layer plus shim, both browser
  routes enter `eglInitialize` and do not return. With
  `RDOC_GPU_LAUNCHER_CLEAR_RENDERDOC_LAYER=1`, Chrome and Electron GPU children
  crash with `exit_code=139` before wrapper EGL/Vulkan telemetry. With
  `RDOC_GPU_LAUNCHER_LAYER_ONLY=1` and no preload shim, both routes still fail
  `missing-rdc` and emit no shim summary by design. Evidence:
  `build/renderdoc/chrome-gpu-egl-init-return-no-layer/html/evidence.env`,
  `build/renderdoc/electron-gpu-egl-init-return-no-layer/electron-html/evidence.env`,
  `build/renderdoc/chrome-gpu-layer-only/html/evidence.env`,
  `build/renderdoc/electron-gpu-layer-only/electron-html/evidence.env`, and
  `doc/09_report/renderdoc_browser_gpu_layer_isolation_2026-06-29.md`.
- 2026-06-29 A diagnostic `--use-gl=angle` flag variant is now reproducible via
  `RDOC_CHROME_EXTRA_VULKAN_FLAGS` and `RDOC_ELECTRON_EXTRA_VULKAN_FLAGS`.
  Fresh Chrome and Electron GPU-child autocapture runs with `--use-gl=angle`
  still report ANGLE status `pass`, enter `eglInitialize`, do not return from
  `eglInitialize`, do not reach `eglChooseConfig` or `vkCreateInstance`, and
  produce no `.rdc`. This rules out missing explicit `--use-gl=angle` selection
  as the current Linux browser RenderDoc blocker. Evidence:
  `build/renderdoc/chrome-gpu-use-gl-angle/html/evidence.env`,
  `build/renderdoc/electron-gpu-use-gl-angle/electron-html/evidence.env`, and
  `doc/09_report/renderdoc_browser_use_gl_angle_2026-06-29.md`.
- 2026-06-29 Superseded by the 2026-07-02 Linux aggregate: this GPU-child
  autocapture route appeared resolved after forcing the Vulkan implicit layer
  search path to the per-run Vulkan-only RenderDoc manifest, but it is not
  current completion proof. The current canonical Chrome and Electron browser
  evidence files exist and both fail the `.rdc` artifact gate; keep
  `renderdoc-chrome-rdc,renderdoc-electron-rdc` blocked until fresh aggregate
  evidence reports `linux_vulkan_render_log_compare_renderdoc_gate_status=pass`
  with `RDOC` magic for both browser artifacts. Historical evidence from the
  superseded run:
  `build/renderdoc/chrome-implicit-layer-default-autocapture/html/evidence.env`,
  `build/renderdoc/electron-implicit-layer-default-autocapture/electron-html/evidence.env`,
  `build/renderdoc/chrome-implicit-layer-default-gate/evidence.env`,
  `build/renderdoc/electron-implicit-layer-default-gate/evidence.env`,
  `build/linux-vulkan-render-log-compare-implicit-layer-default-raw/evidence.env`,
  and `doc/09_report/renderdoc_browser_implicit_layer_capture_2026-06-29.md`.
- 2026-06-29 ANGLE's upstream debugging guide documents
  `RENDERDOC_HOOK_EGL=0` as a Windows workaround and says Linux requires a
  RenderDoc build without GL/GLES support for this EGL-hooking capture issue.
  Local Chrome and Electron probes with `RENDERDOC_HOOK_EGL=0` still report
  `egl_initialize_count=1`, `egl_initialize_return_count=0`, and `missing-rdc`.
  The Linux aggregate now exposes this as
  `linux_vulkan_render_log_compare_renderdoc_linux_angle_workaround_status=needed`
  with reason
  `linux-angle-eglinitialize-does-not-return-under-renderdoc-layer`. Evidence:
  `build/renderdoc/chrome-gpu-egl-hook-off/html/evidence.env`,
  `build/renderdoc/electron-gpu-egl-hook-off/electron-html/evidence.env`, and
  `doc/09_report/renderdoc_browser_linux_angle_egl_hook_2026-06-29.md`.
- 2026-06-29 Added and ran the repo-local Linux Vulkan-only RenderDoc build
  path. `scripts/setup/build-renderdoc-linux-vulkan-only.shs` builds RenderDoc
  `v1.44` with `ENABLE_GL=OFF`, `ENABLE_GLES=OFF`, `ENABLE_EGL=OFF`, and
  `ENABLE_VULKAN=ON`, installs into
  `build/tools/renderdoc-linux-vulkan-only`, and the shared RenderDoc finder
  now prefers that tree on Linux. The built `renderdoccmd --version` reports
  compile-time API support as `Vulkan` only. Chrome and Electron probes against
  this build still report `egl_initialize_count=1`,
  `egl_initialize_return_count=0`, `vk_create_instance=0`, and `missing-rdc`.
  Evidence:
  `build/tools/renderdoc-linux-vulkan-only-build/evidence.env`,
  `build/renderdoc/chrome-gpu-vulkan-only-renderdoc/html/evidence.env`,
  `build/renderdoc/electron-gpu-vulkan-only-renderdoc/electron-html/evidence.env`,
  and `doc/09_report/renderdoc_linux_vulkan_only_build_2026-06-29.md`.
- 2026-06-29 Added a minimal GPU-child delay-trigger preload shim that exports
  no EGL/Vulkan wrapper symbols. `RDOC_GPU_LAUNCHER_DELAY_TRIGGER=1` loads
  `scripts/tool/renderdoc-delay-trigger.c` in the Chromium GPU child, finds
  `RENDERDOC_GetAPI` through loader-lock-free ELF lookup, and calls timed
  `StartFrameCapture`/`EndFrameCapture`. Chrome and Electron both report
  `rdoc_gpu_delay_trigger_loaded_count=1`,
  `rdoc_gpu_delay_trigger_api_ready_count=1`, and
  `rdoc_gpu_delay_trigger_last_end_ok=0`; no `.rdc` is produced. The Linux
  aggregate forwards these delay-trigger fields while keeping
  `renderdoc-chrome-rdc` and `renderdoc-electron-rdc` blocked. Evidence:
  `build/renderdoc/chrome-gpu-delay-trigger-structured-vulkan-only/html/evidence.env`,
  `build/renderdoc/electron-gpu-delay-trigger-structured-vulkan-only/electron-html/evidence.env`,
  and `doc/09_report/renderdoc_browser_delay_trigger_vulkan_only_2026-06-29.md`.
- 2026-06-29 The delay-trigger shim now records RenderDoc capture state. Fresh
  Chrome and Electron runs set the capfile template and reach the API, but
  `IsFrameCapturing()` remains `0` immediately after `StartFrameCapture`,
  `EndFrameCapture` returns `0`, and `GetNumCaptures()` remains `0`. This moves
  the remaining blocker from API discovery to RenderDoc capture arming/ownership
  inside the Chromium GPU child. Evidence:
  `build/renderdoc/chrome-gpu-delay-trigger-state-vulkan-only/html/evidence.env`
  and
  `build/renderdoc/electron-gpu-delay-trigger-state-vulkan-only/electron-html/evidence.env`.
- The direct Chrome/Electron RenderDoc wrapper now records
  `rdoc_renderdoc_hook_children` and accepts `RDOC_RENDERDOC_HOOK_CHILDREN=0`
  to omit `--opt-hook-children`. This confirms the immediate Chrome GPU crash
  is tied to RenderDoc child-process hooking: the no-child Chrome run avoids
  `exit_code=139`, but still fails `missing-rdc` because Chromium's Vulkan work
  stays in the GPU child process. Evidence:
  `build/renderdoc/chrome-no-child-hook-renderdoc-display/html/evidence.env`.
  Electron no-child-hook capture also fails `missing-rdc` and is diagnostic
  only:
  `build/renderdoc/electron-no-child-hook-renderdoc-display/electron-html/evidence.env`.
- The same `--no-zygote` path exposed a separate Electron evidence bug:
  Electron wrote ARGB output relative to the Electron binary directory when the
  helper passed a relative path. The helper now passes absolute ARGB and stage
  paths. The current Electron display-helper evidence records a nonblank
  1280x720 ARGB file with 405674 nonblank pixels under RenderDoc launch, but
  still fails the gate because `.rdc` is missing:
  `build/renderdoc/electron-display-helper/electron-html/evidence.env`.

2026-06-26 target-control evidence hardening:
- `scripts/check/check-renderdoc-chrome-target-control.shs` now records
  Chromium GPU-process diagnostics before invoking qrenderdoc target control:
  `rdoc_chrome_target_control_gpu_env_has_layer`,
  `rdoc_chrome_target_control_gpu_maps_has_renderdoc`, and
  `rdoc_chrome_target_control_gpu_maps_has_vulkan`.
- The same wrapper now fails closed with
  `rdoc_chrome_target_control_reason=no-gpu-process` when Chrome does not spawn
  a GPU process, so qrenderdoc cannot accidentally trigger capture on an
  unrelated RenderDoc target.
- The executable contract is covered by
  `test/03_system/check/renderdoc_chrome_target_control_spec.spl` and mirrored
  in `doc/06_spec/test/03_system/check/renderdoc_chrome_target_control_spec.md`.

2026-06-27 current aggregate state after browser-backing and perf refresh:
- Browser Vulkan backing is no longer the Linux blocker on the current NVIDIA
  host. The focused browser-backing lane reports:
  `gui_web_2d_vulkan_browser_backing_status=pass`,
  `gui_web_2d_vulkan_electron_browser_backing_status=pass`, and
  `gui_web_2d_vulkan_chrome_browser_backing_status=pass`.
- Retained GUI showcase performance is current after the wrapper provenance
  fix. Strict aggregate freshness reports
  `gui_showcase_4k_200fps_source_revision_status=current` and
  `gui_showcase_8k_perf_source_revision_status=current` for source revision
  `74744b04ae2d`.
- Linux normalized render-log comparison still fails only on browser RenderDoc
  artifacts after Simple `.rdc` proof:
  `linux_vulkan_render_log_compare_renderdoc_simple_status=pass`,
  `linux_vulkan_render_log_compare_renderdoc_simple_artifact_magic=RDOC`,
  `linux_vulkan_render_log_compare_renderdoc_chrome_status=fail`,
  `linux_vulkan_render_log_compare_renderdoc_chrome_reason=chromium-gpu-process-crashed-under-renderdoc`,
  `linux_vulkan_render_log_compare_renderdoc_chrome_artifact_file_status=missing`,
  `linux_vulkan_render_log_compare_renderdoc_electron_status=fail`, and
  `linux_vulkan_render_log_compare_renderdoc_electron_reason=missing-rdc`.
- The aggregate blocker count remains eight because Linux browser `.rdc`
  capture, Electron widget `.rdc`, cross-platform native render-log comparison,
  production GUI/web parity/readback, and full CSS rendering coverage are still
  incomplete.

Next Linux verification criteria:
- Do not rerun broad diagnostics unless a new capture mechanism is being tested.
  A successful Linux unblock must produce Chrome and Electron `.rdc` artifacts
  whose top-level Linux evidence has
  `linux_vulkan_render_log_compare_renderdoc_chrome_artifact_file_status=pass`,
  `linux_vulkan_render_log_compare_renderdoc_chrome_artifact_magic=RDOC`,
  `linux_vulkan_render_log_compare_renderdoc_electron_artifact_file_status=pass`,
  and `linux_vulkan_render_log_compare_renderdoc_electron_artifact_magic=RDOC`.
- Browser backing, ARGB source, pairwise diff, and Simple RenderDoc gates must
  remain passing in the same aggregate run; do not treat a browser `.rdc` as a
  full Linux pass if it breaks Vulkan backing or pixel comparison.

2026-07-02 current Linux refresh:
- Direct GUI/Web/2D Vulkan evidence now exists at
  `build/gui-web-2d-vulkan-env-run-current/evidence.env` and passes Simple
  Vulkan, browser backing, ARGB source, and pairwise ARGB diff gates.
- Simple RenderDoc evidence remains passing with `RDOC` magic at
  `build/gui-web-2d-vulkan-env-renderdoc-simple/renderdoc/simple/evidence.env`.
- Canonical browser RenderDoc evidence files now exist but fail the `.rdc`
  artifact gate:
  `build/renderdoc/chrome-implicit-layer-default-autocapture/html/evidence.env`
  and
  `build/renderdoc/electron-implicit-layer-default-autocapture/electron-html/evidence.env`.
- Both canonical browser captures report Chromium GPU process exits with code
  `139` and `rdoc_capture_reason=missing-rdc`. Chrome now records
  `rdoc_chromium_gpu_process_exit_reason=gpu-process-segv-in-renderdoc` with
  `rdoc_chromium_gpu_process_exit_renderdoc_stack_status=fail` and stack count
  `6`; Electron records `gpu-process-exited-unexpectedly` without RenderDoc
  stack frames in the wrapper log.
- `RDOC_CHROME_USE_XVFB=1` with the default child hook was tested as a
  diagnostic at
  `build/renderdoc/chrome-xvfb-default-hook-diagnostic/html/evidence.env`; it
  still exits with code `139`, includes `librenderdoc.so` frames, and emits no
  `.rdc`.
- `RDOC_RENDERDOC_HOOK_CHILDREN=0` diagnostic runs avoid the GPU-process exit
  for Chrome and Electron but still produce no `.rdc`; Electron also times out
  on shutdown with exit `124`. Current diagnostic evidence:
  `build/renderdoc/chrome-implicit-layer-no-child-hook-diagnostic/html/evidence.env`
  and
  `build/renderdoc/electron-implicit-layer-no-child-hook-diagnostic/electron-html/evidence.env`.
- Current top-level compare remains failed with only
  `renderdoc-chrome-rdc,renderdoc-electron-rdc` blocked. Evidence:
  `doc/09_report/linux_vulkan_render_log_compare_current_2026-07-02.md`.
- Current blocking keys:
  `linux_vulkan_render_log_compare_status=fail`,
  `linux_vulkan_render_log_compare_blocked_gates=renderdoc-chrome-rdc,renderdoc-electron-rdc`,
  `linux_vulkan_render_log_compare_renderdoc_chrome_reason=chromium-gpu-process-segv-in-renderdoc`,
  `linux_vulkan_render_log_compare_renderdoc_chrome_gpu_process_exit_codes=139`,
  `linux_vulkan_render_log_compare_renderdoc_chrome_gpu_process_exit_renderdoc_stack_status=fail`,
  `linux_vulkan_render_log_compare_renderdoc_chrome_artifact_magic=missing`,
  `linux_vulkan_render_log_compare_renderdoc_electron_gpu_process_exit_codes=139`,
  and `linux_vulkan_render_log_compare_renderdoc_electron_artifact_magic=missing`.

2026-07-03 current aggregate supersedes the 2026-07-02 blocked state:
- `doc/09_report/linux_renderdoc_simpleos_hardening_evidence_current_2026-07-02.md`
  reports `status: pass`, `blocked_gate_count: 0`, and
  `renderdoc_gate_status: pass`.
- Local artifact magic was rechecked on 2026-07-03 for the canonical Simple,
  Chrome, and Electron captures:
  `build/renderdoc/canonical-probe/simple/simple_gui_app_capture.rdc`,
  `build/renderdoc/chrome-implicit-layer-default-autocapture/html/gpu_chrome_capture.rdc`,
  and
  `build/renderdoc/electron-implicit-layer-default-autocapture/electron-html/electron_gpu_capture.rdc`
  all begin with `RDOC`.
- The focused contract is covered by
  `test/03_system/check/linux_vulkan_renderdoc_reason_forwarding_spec.spl`,
  which now keeps both the forwarding contract and the current unblocked
  aggregate state pinned.
