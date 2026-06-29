# RenderDoc Browser Delay Trigger Vulkan-Only Evidence - 2026-06-29

## Change

Added a minimal GPU-child preload shim:
`scripts/tool/renderdoc-delay-trigger.c`.

The shim is enabled through `scripts/tool/renderdoc-gpu-launcher.shs` with:

```text
RDOC_GPU_LAUNCHER_DELAY_TRIGGER=1
```

Unlike `renderdoc-vulkan-autocapture.c`, this shim exports no EGL or Vulkan
wrapper symbols. It waits inside the Chromium GPU child, locates
`RENDERDOC_GetAPI` through a loader-lock-free ELF lookup against the already
loaded `librenderdoc.so`, then calls `StartFrameCapture` and
`EndFrameCapture`.

## Chrome Probe

Evidence:
`build/renderdoc/chrome-gpu-delay-trigger-structured-vulkan-only/html/evidence.env`.

Key result:

```text
rdoc_gpu_delay_trigger_loaded_count=1
rdoc_gpu_delay_trigger_api_ready_count=1
rdoc_gpu_delay_trigger_last_end_ok=0
rdoc_gpu_delay_trigger_elf_status=rdoc_delay_trigger_elf=symbol-found
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
rdoc_capture_magic=
```

The longer Chrome timing probe at
`build/renderdoc/chrome-gpu-delay-trigger-late-vulkan-only/html/evidence.env`
also reached the API and returned `EndFrameCapture ok=0`.

## Electron Probe

Evidence:
`build/renderdoc/electron-gpu-delay-trigger-structured-vulkan-only/electron-html/evidence.env`.

Key result:

```text
rdoc_gpu_delay_trigger_loaded_count=1
rdoc_gpu_delay_trigger_api_ready_count=1
rdoc_gpu_delay_trigger_last_end_ok=0
rdoc_gpu_delay_trigger_elf_status=rdoc_delay_trigger_elf=symbol-found
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
rdoc_capture_magic=
```

## Aggregate

Focused aggregate:
`build/linux-vulkan-render-log-compare/evidence.env`.

The Linux aggregate now forwards:

```text
linux_vulkan_render_log_compare_renderdoc_chrome_delay_trigger_loaded_count=1
linux_vulkan_render_log_compare_renderdoc_chrome_delay_trigger_api_ready_count=1
linux_vulkan_render_log_compare_renderdoc_chrome_delay_trigger_last_end_ok=0
linux_vulkan_render_log_compare_renderdoc_electron_delay_trigger_loaded_count=1
linux_vulkan_render_log_compare_renderdoc_electron_delay_trigger_api_ready_count=1
linux_vulkan_render_log_compare_renderdoc_electron_delay_trigger_last_end_ok=0
```

`renderdoc-chrome-rdc` and `renderdoc-electron-rdc` remain blocked because no
valid `RDOC` artifact is produced.

## Related Hotkey Probe

`doc/09_report/renderdoc_chrome_x11_layer_hotkey_2026-06-29.md` records that
the Vulkan-only RenderDoc layer loads into the Chrome GPU process through the
GPU launcher, but X11 hotkey delivery targets the browser-owned window instead
of the GPU process. That route also remains diagnostic only.

## Interpretation

The Linux browser blocker has moved past API discovery: a minimal, non-EGL,
non-Vulkan-wrapper preload shim can reach the RenderDoc API in the Chromium GPU
child using the Vulkan-only RenderDoc build. RenderDoc still declines the timed
capture with `EndFrameCapture ok=0`, leaving the next debugging target at
RenderDoc capture ownership/active frame state inside the GPU child rather than
EGL symbol interposition alone.
