# GUI/Web/2D Vulkan Setup

This guide records host setup for the GUI/Web/2D Vulkan comparison lane. Use it
with `scripts/setup/setup-gui-web-2d-vulkan-env.shs`.

## Current 2026-07-02 Completion Status

Older Linux rows in this guide are historical setup and diagnostic evidence.
They do not prove current final completion. Final Linux completion requires a
fresh aggregate run with source-aligned evidence, current Chrome/Electron/Simple
artifacts, and real RenderDoc `.rdc` files with `RDOC` magic for every required
RenderDoc gate. Browser backing, direct ARGB comparison, or retained 4K/8K
performance rows are supporting evidence only until the `.rdc` gates pass.
The current retained aggregate is
`doc/09_report/linux_vulkan_render_log_compare_current_2026-07-02.md`: Simple
Vulkan, browser backing, pairwise ARGB diff, and Simple RenderDoc pass, but
`renderdoc-chrome-rdc,renderdoc-electron-rdc` remain blocked by Chromium GPU
process exit code `139` under RenderDoc and missing browser `.rdc` artifacts.

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

For the SimpleOS multi-config lane, the Windows evidence wrapper can record the
same host readiness diagnostics without claiming browser or SimpleOS Vulkan
proof:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-multiconfig-live-evidence.ps1 -ProbeHostVulkan
```

Expected diagnostic rows include `simpleos_windows_vulkaninfo_status`,
`simpleos_windows_vulkan_sdk_tools_status`,
`simpleos_windows_renderdoc_tool_status`,
`simpleos_windows_vulkan_host_readiness_status`, and the required
`gui_web_2d_vulkan_browser_backing_*` rows. A passing `vulkaninfo` row is host
readiness only; missing SDK tools, missing RenderDoc, or failed focused browser
backing keeps the Vulkan/RenderDoc evidence incomplete.

When the SimpleOS multi-config Engine2D/RenderDoc normalizer consumes
`build/gui-web-2d-vulkan-env/evidence.env`, it also emits
`simpleos_engine2d_source_evidence_usable_status` and
`simpleos_engine2d_source_evidence_usable_reason`. A source file produced only
by `--browser-backing`, especially with `gui_web_2d_vulkan_simple_status=not-run`,
must remain blocked as `source-browser-backing-only-simple-not-run`; it is not
SimpleOS Engine2D Vulkan proof. Missing `.rdc` and WM RenderDoc logs are exposed
through `simpleos_renderdoc_artifact_blocker_reason` and
`simpleos_wm_renderdoc_log_compare_reason`.

On Windows, where `sh` may be unavailable, use the native Simple Vulkan
readback probe instead of the Unix `.shs` wrapper:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-vulkan-engine2d-readback.ps1 -SimpleBinary bin\simple.exe
```

The SimpleOS Engine2D/RenderDoc normalizer can run that probe directly:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-engine2d-renderdoc-evidence.ps1 -RunSimpleVulkanProbe -SimpleBinary bin\simple.exe -ProbeHostVulkan
```

or through the combined SimpleOS wrapper with `-RunSimpleVulkanProbe`. Passing
evidence requires `vulkan_engine2d_readback_status=pass`,
`vulkan_engine2d_readback_spec_status=pass`, and
`vulkan_engine2d_readback_backend_name=vulkan`. A timeout is recorded as
`vulkan_engine2d_readback_reason=evidence-program-timeout` and remains blocked;
the normalizer reports
`simpleos_engine2d_source_evidence_usable_reason=direct-simple-vulkan-readback-evidence-program-timeout`.
The Windows wrapper also refuses to launch a new Simple child when the host
already has more than 128 `simple.exe` processes, unless explicitly overridden
with `-AllowHighSimpleProcessCount`. That condition is reported as
`vulkan_engine2d_readback_reason=existing-simple-process-count-high` plus the
count/limit rows, and the SimpleOS aggregate echoes
`simpleos_engine2d_direct_readback_existing_simple_process_count` and
`simpleos_engine2d_direct_readback_existing_simple_process_limit`.
Use `-PreflightOnly -AllowHighSimpleProcessCount` to record only the process
state without launching a Simple child; the normalizer reports
`simpleos_engine2d_direct_readback_reason=preflight-only`. The SimpleOS
aggregate also echoes the Engine2D bridge/backend rows, Vulkan device name,
viewport, checksum, nonblank status, and QEMU GPU readback path/dimensions from
that merged file. A preflight-only run can prove the current QEMU framebuffer
artifact is present and nonblank while still leaving
`simpleos_engine2d_vulkan_evidence_status` blocked until a real Simple Vulkan
Engine2D readback passes.
The Engine2D normalizer also emits source-audit rows:
`simpleos_engine2d_source_qemu_entry_status`,
`simpleos_engine2d_source_baremetal_core_status`,
`simpleos_engine2d_source_virtio_surface_status`,
`simpleos_engine2d_source_vulkan_session_status`, and
`simpleos_engine2d_source_bridge_audit_status`. The current expected blocked
audit is `blocked:desktop-service-not-wired-to-vulkan-engine2d-session`; it
means the source surfaces are present but the QEMU desktop-service draw path is
still the freestanding display runtime, not proven Vulkan Engine2D.

For a standalone process inventory, run the dry-run helper:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simple-process-inventory.ps1
```

It writes `simple_process_inventory_*` rows and does not terminate processes by
default. Cleanup is intentionally explicit: use `-Kill
-ConfirmText KILL_SIMPLE_PROCESSES` only after reviewing the dry-run evidence
and deciding those `simple.exe` processes are safe to stop.

The same SimpleOS multi-config Windows wrapper can record FPGA serial-port
inventory diagnostics without claiming a board boot:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-multiconfig-live-evidence.ps1 -ProbeFpgaSerialPorts
```

This forwards `-ProbeSerialPorts` to
`scripts\check\check-simpleos-fpga-rv64-serial-evidence.ps1` and emits
`simpleos_fpga_serial_port_probe_*` plus
`simpleos_fpga_serial_device_candidate_status`. These rows are inventory only;
the FPGA UART terminal gate still requires a real serial log containing the
boot marker.

To collect that UART log directly from Windows, use the opt-in bounded capture
mode:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-fpga-rv64-serial-evidence.ps1 -CaptureSerial -SerialDevice COM3 -CaptureTimeoutSeconds 30
```

or through the combined wrapper:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-multiconfig-live-evidence.ps1 -CaptureFpgaSerial -FpgaSerialDevice COM3 -FpgaSerialCaptureTimeoutSeconds 30
```

Capture writes `simpleos_fpga_serial_capture_*` rows. It is still fail-closed:
the FPGA UART terminal gate passes only when the captured or supplied log
contains `SIMPLEOS_FPGA_RISCV64_SERIAL_BOOT` and the toolchain/bitstream rows
also pass.

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

## Current Linux RenderDoc Evidence - 2026-07-02

Current combined evidence is indexed in
`doc/09_report/linux_renderdoc_simpleos_hardening_evidence_current_2026-07-02.md`.
For Linux it points at `doc/09_report/linux_vulkan_render_log_compare_2026-06-29.md`,
which records:

- `linux_vulkan_render_log_compare_blocked_gate_count=0`
- `linux_vulkan_render_log_compare_renderdoc_gate_status=pass`
- Simple, Chrome, and Electron artifacts all report `RDOC` magic
- Vulkan Engine2D readback and CPU SIMD Engine2D reports both pass with zero
  mismatches

Treat the 2026-06-27 missing-`renderdoccmd` rows as historical host-local
blockers, not the current Linux completion state.

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
