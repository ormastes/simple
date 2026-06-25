# GUI/Web/2D Vulkan Setup

This guide records host setup for the GUI/Web/2D Vulkan comparison lane. Use it
with `scripts/setup/setup-gui-web-2d-vulkan-env.shs`.

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

## Full Evidence

After SDK tools and browser backing are ready, use:

```sh
scripts/setup/setup-gui-web-2d-vulkan-env.shs --check
scripts/setup/setup-gui-web-2d-vulkan-env.shs --browser-backing
scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
```

Use `--renderdoc-simple` or `--renderdoc` only on a prepared RenderDoc host.
Do not run broad Simple checks while a runaway `bin/simple` process tree is
present; record setup readiness and defer runtime evidence instead.
