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
  shim only records `rdoc_autocapture_loaded=1`; Chromium does not reach the
  wrapped Vulkan queue submit/present hooks before timeout/failure, so no
  `.rdc` is produced. Evidence:
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
