# GUI/Web/2D Vulkan Setup

This guide records host setup for the GUI/Web/2D Vulkan comparison lane. Use it
with `scripts/setup/setup-gui-web-2d-vulkan-env.shs`.

## Current 2026-06-28 Completion Status

Older Linux rows in this guide are historical setup and diagnostic evidence.
They do not prove current final completion. Final Linux completion requires a
fresh aggregate run with source-aligned evidence, current Chrome/Electron/Simple
artifacts, and real RenderDoc `.rdc` files with `RDOC` magic for every required
RenderDoc gate. Browser backing, direct ARGB comparison, or retained 4K/8K
performance rows are supporting evidence only until the `.rdc` gates pass.

## Windows Status

Observed on 2026-06-22:

- Vulkan runtime/driver is installed: `vulkaninfo --summary` reports Vulkan
  Instance Version `1.3.301`.
- The visible Vulkan devices are Intel UHD Graphics 770, API version `1.3.284`,
  driver `101.5592`.
- Chrome is installed at
  `C:\Program Files\Google\Chrome\Application\chrome.exe`, version
  `149.0.7827.155`.
- Electron is installed globally as `electron`, version `v32.1.2`.
- DirectX tooling is present through `dxdiag`, but DirectX availability is not
  Vulkan proof.
- Vulkan SDK developer tools are not ready until `glslangValidator`,
  `spirv-as`, and any required shader compiler such as `dxc` are visible to the
  shell used by the evidence wrapper.

The attempted command:

```powershell
winget install --id KhronosGroup.VulkanSDK --accept-source-agreements --accept-package-agreements --silent
```

downloaded and hash-verified Vulkan SDK `1.4.350.0`, then reached an
administrator installer prompt and was canceled. Treat the host as
`sdk-tools-missing` until the elevated install completes and a fresh shell can
find the SDK tools.

## Linux Status (Ubuntu) — verified 2026-06-25

Observed on an Ubuntu 24.04.3 host, Intel Raptor Lake-P (RPL-P) iGPU. This is
historical setup evidence for the previously-deferred Linux leg: **Electron and
Chrome were confirmed rendering through Vulkan**, and the RenderDoc CLI was
installed and Vulkan-capable. Treat it as setup history, not current final
completion evidence.

- **Vulkan runtime/driver: READY.** `vulkaninfo --summary` reports `Intel(R) Graphics
  (RPL-P)`, `apiVersion = 1.4.318`, `driverName = Intel open-source Mesa driver` (Mesa
  ANV), `llvmpipe` software fallback. ICD `/usr/share/vulkan/icd.d/intel_icd.json`.
- **Electron: VULKAN-BACKED, CONFIRMED.** `~/electron-vulkan` (Electron `v42.5.0`).
  `app.getGPUFeatureStatus().vulkan == "enabled_on"`; live WebGL `UNMASKED_RENDERER`
  = `ANGLE (Intel, Vulkan 1.4.318 (Intel(R) Graphics (RPL-P)), Intel open-source Mesa
  driver)`. `node_modules/electron/dist/chrome-sandbox` set `root:root` mode `4755`.
- **Chrome: VULKAN-BACKED, CONFIRMED.** `google-chrome-stable 139.0.7258.138`; same
  ANGLE-Vulkan renderer, read via the DevTools `/json` endpoint. Vulkan is **not** on
  by default — it requires the launch flags below.
- **RenderDoc: INSTALLED + VULKAN-CAPABLE.** `renderdoccmd`/`qrenderdoc` `v1.44` at
  `/opt/renderdoc` (on `PATH`); `renderdoccmd version` → `APIs supported at compile-time:
  Vulkan, GL, GLES`. **Not yet proven by an actual `.rdc` capture** on this host (see
  blocker). Treat as `renderdoc-installed`, capture-evidence pending.

### CRITICAL gotcha — Wayland is incompatible with Chromium Vulkan

This is a Wayland session. Chromium's Vulkan path is **not** compatible with the Wayland
Ozone backend; without forcing X11 the GPU process silently falls back to software and
Vulkan stays `disabled_off`. Mandatory flag set for **both** Electron and Chrome:

```sh
--ozone-platform=x11 --use-angle=vulkan \
--enable-features=Vulkan,DefaultANGLEVulkan,VulkanFromANGLE --ignore-gpu-blocklist
```

### RenderDoc-capture blocker (Chrome) — record, do not retry blindly

Current Linux evidence shows Chrome and Electron still fail the browser
RenderDoc `.rdc` gates with Chromium GPU-process exit code `139`. Chrome's log
now classifies the failure as
`rdoc_chromium_gpu_process_exit_reason=gpu-process-segv-in-renderdoc` when the
crash stack includes `librenderdoc.so`; Electron may only expose
`gpu-process-exited-unexpectedly`. Keep
`renderdoc-chrome-rdc,renderdoc-electron-rdc` blocked until both capture files
exist and report `rdoc_capture_magic=RDOC`.

## Linux Install Commands (Ubuntu/Debian)

```sh
sudo apt-get update
sudo apt-get install -y mesa-vulkan-drivers vulkan-tools vulkan-validationlayers libvulkan-dev

# RenderDoc (not in apt — official binary tarball)
# download renderdoc_1.44.tar.gz from renderdoc.org/stable/1.44/, then:
sudo tar xzf renderdoc_1.44.tar.gz -C /opt && sudo mv /opt/renderdoc_1.44 /opt/renderdoc
sudo ln -sf /opt/renderdoc/bin/qrenderdoc /usr/local/bin/qrenderdoc
sudo ln -sf /opt/renderdoc/bin/renderdoccmd /usr/local/bin/renderdoccmd

# Electron needs Node >= 22 (modern installer is ESM-only; breaks on Node 18/20).
cd ~/electron-vulkan && npm install --save-dev electron
sudo chown root:root node_modules/electron/dist/chrome-sandbox
sudo chmod 4755     node_modules/electron/dist/chrome-sandbox
# Google Chrome: install google-chrome-stable from the google-chrome apt repo.
```

## Linux Readiness Checks

```sh
vulkaninfo --summary | grep -E 'deviceName|driverName|apiVersion'
~/electron-vulkan/node_modules/.bin/electron --version
google-chrome-stable --version
renderdoccmd version | head -2
# Prove Electron Vulkan (expects vulkan: enabled_on + ANGLE Vulkan renderer):
cd ~/electron-vulkan && ./node_modules/.bin/electron gpu-probe.js --ozone-platform=x11
# Prove Chrome Vulkan: launch with the flag set above + --remote-debugging-port=9222 on a
# WebGL page, then read the renderer from http://localhost:9222/json (title field).
```

`vulkaninfo --summary` proves host Vulkan discovery only — NOT that Chrome/Electron render
through Vulkan. Use the Electron `gpu-probe.js` and the Chrome DevTools read for that.

## Install Commands

Windows PowerShell:

```powershell
winget install --id KhronosGroup.VulkanSDK --accept-source-agreements --accept-package-agreements
winget install --id Google.Chrome --accept-source-agreements --accept-package-agreements
winget install --id OpenJS.NodeJS.LTS --accept-source-agreements --accept-package-agreements
npm install -g electron
```

Optional DirectX shader compiler setup depends on the local toolchain policy.
Do not mark `dxc` ready until `Get-Command dxc` resolves in the same shell used
by the build or evidence wrapper.

## Readiness Checks

Use these host checks before launching any repo runtime:

```powershell
vulkaninfo --summary
Get-Command glslangValidator
Get-Command spirv-as
Get-Command dxc
& 'C:\Program Files\Google\Chrome\Application\chrome.exe' --version
electron --version
dxdiag /whql:off /t "$env:TEMP\dxdiag-simple-vulkan.txt"
```

`vulkaninfo --summary` proves host Vulkan runtime/device discovery. It does not
prove Simple, Chrome, or Electron render through Vulkan.

## Browser Vulkan Proof

Chrome or Electron being installed is not enough. A bitmap, screenshot, or
DirectX report is also not enough. Browser Vulkan proof must come from the
evidence keys emitted by:

```sh
scripts/setup/setup-gui-web-2d-vulkan-env.shs --browser-backing
```

Required keys:

- `gui_web_2d_vulkan_browser_backing_status`
- `gui_web_2d_vulkan_browser_backing_reason`
- `gui_web_2d_vulkan_browser_backing_mode`

Exact pixel parity between Simple, Chrome, and Electron is still fallback
bitmap evidence. It does not satisfy browser Vulkan proof by itself. If focused
browser proof is missing, record:

- `gui_web_2d_vulkan_browser_backing_status=fail`
- `gui_web_2d_vulkan_browser_backing_mode=focused-browser-backing-required`
- `gui_web_2d_vulkan_browser_backing_reason=missing-focused-browser-backing`

If Chrome or Electron logs `angle=vulkan` unavailable or falls back to a
non-Vulkan path, record `vulkan-angle-unavailable` and leave the browser Vulkan
gate failed.

## Current Linux Browser-Backing Evidence - 2026-06-26

The current Linux host produced a focused browser-backing pass with:

```sh
GUI_WEB_2D_VULKAN_BUILD_DIR=build/gui-web-2d-vulkan-env-browser-backing-current \
sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --browser-backing
```

Retained report:
`doc/09_report/gui_web_2d_vulkan_browser_backing_2026-06-26_current.md`.

Key rows:

- `gui_web_2d_vulkan_browser_backing_status=pass`
- `gui_web_2d_vulkan_browser_backing_mode=gpu-feature-status`
- `gui_web_2d_vulkan_electron_browser_backing_status=pass`
- `gui_web_2d_vulkan_chrome_browser_backing_status=pass`
- Electron and Chrome both reported `ANGLE_VULKAN` and `GaneshVulkan`
- Renderer: NVIDIA Vulkan `1.4.312` on NVIDIA TITAN RTX, driver `580.126.16.0`

This satisfies the focused browser Vulkan backing gate when the aggregate is run
with
`GUI_WEB_2D_VULKAN_BROWSER_BACKING_EVIDENCE_ENV=build/gui-web-2d-vulkan-env-browser-backing-current/evidence.env`.
It does not satisfy RenderDoc `.rdc`, PIX, GPU debugger, or native render-log
capture gates.

## Linux Perf And RenderDoc Snapshot - 2026-06-27

This is a dated snapshot, not a standing completion claim. Re-run the wrappers
below on the target GUI host before using any row as release or goal evidence.

Retained report:
`doc/09_report/gui_renderdoc_current_perf_browser_renderdoc_blocker_2026-06-27.md`.

Current-source retained showcase rows pass at source revision `56a1985b1d38`:

- `gui_showcase_4k_200fps_status=pass`
- `gui_showcase_4k_200fps_source_revision_status=current`
- `gui_showcase_8k_perf_status=pass`
- `gui_showcase_8k_perf_source_revision_status=current`

The host has hardware Vulkan through NVIDIA:

- `gui_web_2d_vulkan_loader_status=present`
- `gui_web_2d_vulkan_device=NVIDIA TITAN RTX`
- `gui_web_2d_vulkan_driver=NVIDIA`

RenderDoc capture is still blocked on this host:

- `gui_web_2d_vulkan_renderdoc_status=unavailable`
- `gui_web_2d_vulkan_renderdoc_reason=missing-renderdoccmd-in-search-paths`

Do not claim `.rdc` capture completion from browser backing or 4K/8K retained
perf rows. Install or expose `renderdoccmd` first, then run
`scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc-simple` or the full
`--renderdoc` path.

Readiness evidence and current blockers must stay separate: `--check` proves
loader/tool discovery, `--browser-backing` proves Chromium GPU metadata,
`--run` proves direct ARGB comparison, and `--renderdoc`/`--renderdoc-simple`
are the only Linux paths that can produce native `.rdc` completion evidence.

## Full Evidence

After SDK tools and browser backing are ready, use:

```sh
GUI_WEB_2D_VULKAN_BUILD_DIR=build/gui-web-2d-vulkan-env-check-current \
  scripts/setup/setup-gui-web-2d-vulkan-env.shs --check
GUI_WEB_2D_VULKAN_BUILD_DIR=build/gui-web-2d-vulkan-env-browser-backing \
  scripts/setup/setup-gui-web-2d-vulkan-env.shs --browser-backing
GUI_WEB_2D_VULKAN_BUILD_DIR=build/gui-web-2d-vulkan-env-run-current \
  scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
GUI_WEB_2D_VULKAN_BUILD_DIR=build/gui-web-2d-vulkan-env-renderdoc-simple \
  scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc-simple
RDOC_OUTPUT_DIR=build/renderdoc/chrome-implicit-layer-default-autocapture \
  scripts/tool/renderdoc-evidence.shs capture-html
RDOC_OUTPUT_DIR=build/renderdoc/electron-implicit-layer-default-autocapture \
  scripts/tool/renderdoc-evidence.shs capture-electron-html
sh scripts/check/check-linux-vulkan-render-log-compare.shs
RUN_TOKEN=$(date -u +%Y%m%d%H%M%S)
GUI_RENDERDOC_AGGREGATE_DISABLE_DEFAULT_STATIC_CACHE=1 \
GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/gui-web-2d-final-${RUN_TOKEN}/static-cache \
BUILD_DIR=build/gui-web-2d-final-${RUN_TOKEN}/out \
REPORT_PATH=build/gui-web-2d-final-${RUN_TOKEN}/report.md \
  sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

For final completion, do not set
`GUI_RENDERDOC_AGGREGATE_READONLY_STATIC_CACHE_DIR`. Read-only seeded cache is a
fast repeated-check optimization, not native-host proof. The final aggregate
must consume fresh target-host evidence rows and expose byte-level artifact
proof, including `RDOC` magic for required RenderDoc `.rdc` files, `PIX` magic
for Windows PIX artifacts, and Xcode GPU capture magic for macOS capture lanes.
Browser backing, direct ARGB parity, and retained 4K/8K rows remain necessary
but are not substitutes for those capture artifacts.

On clean jj worktrees where repo-local `bin/simple` is absent and same-repo
PATH detection cannot use git metadata, set `ALLOW_PATH_SIMPLE_BIN=1` for the
direct `--run` probe. The setup helper records
`gui_web_2d_vulkan_simple_bin_selection_reason=default-missing-path-opt-in` so
the fallback is visible in retained evidence. Prefer explicit `SIMPLE_BIN=...`
when validating a freshly built self-hosted driver. Rust seed binaries under
`src/compiler_rust/**` are not valid Simple-lane evidence for this wrapper; the
helper records them as `gui_web_2d_vulkan_simple_bin_status=forbidden` and does
not execute them.

Use `--renderdoc-simple` or `--renderdoc` only on a prepared RenderDoc host.
Do not run broad Simple checks while a runaway `bin/simple` process tree is
present; record setup readiness and defer runtime evidence instead.
