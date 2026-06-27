# GUI/Web/2D Linux RenderDoc Host Blocker - 2026-06-27

## Summary

The current Linux host is suitable for Vulkan readiness, browser-backing, and
direct Electron/Chrome/Simple ARGB parity checks, but this session cannot
produce RenderDoc `.rdc` completion evidence because RenderDoc command-line
tooling is not discoverable.

This is a current-session host dependency blocker, not a renderer pass or fail.
Older reports that found RenderDoc tooling are dated diagnostics and must not be
used as current completion proof without fresh command discovery and `.rdc`
artifacts.

## Fresh Host Check

Command:

```sh
BUILD_DIR=build/gui-web-2d-vulkan-env-renderdoc-host-check-2026-06-27 \
sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --check
```

Accepted readiness rows from
`build/gui-web-2d-vulkan-env-renderdoc-host-check-2026-06-27/evidence.env`:

```text
gui_web_2d_vulkan_loader_status=present
gui_web_2d_vulkan_device=NVIDIA TITAN RTX
gui_web_2d_vulkan_driver=NVIDIA
gui_web_2d_vulkan_device_type=PHYSICAL_DEVICE_TYPE_DISCRETE_GPU
gui_web_2d_vulkan_device_selection_status=hardware
gui_web_2d_vulkan_chrome=/home/ormastes/.cache/ms-playwright/chromium-1223/chrome-linux64/chrome
gui_web_2d_vulkan_electron=/tmp/simple-rendering-parallel-plan/tools/electron-shell/node_modules/.bin/electron
```

Blocking RenderDoc rows:

```text
gui_web_2d_vulkan_renderdoc_status=unavailable
gui_web_2d_vulkan_renderdoc_reason=missing-renderdoccmd-in-search-paths
gui_web_2d_vulkan_renderdoc_setup_reason=missing-renderdoccmd-in-search-paths
gui_web_2d_vulkan_renderdoc_cmd=
```

Additional install context from this user session:

```text
command -v renderdoccmd -> missing
command -v renderdoc -> missing
command -v qrenderdoc -> missing
sudo -n true -> sudo_passwordless=no
apt-cache policy renderdoc -> no local package row
```

## Already Proven Without RenderDoc

Use
`doc/09_report/gui_web_2d_linux_vulkan_refresh_2026-06-27.md` as the current
baseline for host-runnable non-RenderDoc evidence. It records passing browser
Vulkan backing, direct Electron/Chrome/Simple ARGB comparison artifacts,
pairwise pixel equivalence, Web WM modern shell evidence, and current-source
4K/8K retained performance rows.

## Still Blocked

The Linux RenderDoc lane remains blocked until a prepared Ubuntu GUI host has
`renderdoccmd` available on `PATH` or under `RDOC_HOME`, and the following
captures produce real `.rdc` files with `RDOC` magic:

- `scripts/tool/renderdoc-evidence.shs capture-simple`
- `scripts/tool/renderdoc-evidence.shs capture-html`
- `scripts/tool/renderdoc-evidence.shs capture-electron-html`

Only after those artifacts exist should a platform agent run:

```sh
LINUX_VULKAN_RENDER_LOG_REQUIRE_RDOC=1 \
sh scripts/check/check-linux-vulkan-render-log-compare.shs
```

Fallback screenshots, launch flags, Chromium installation, and env rows without
`RDOC` magic are not completion evidence for this blocker.
