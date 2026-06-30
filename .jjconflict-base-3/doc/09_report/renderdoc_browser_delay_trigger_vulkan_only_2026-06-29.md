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
`EndFrameCapture`. With `RDOC_GPU_LAUNCHER_DELAY_TRIGGER_MODE=trigger`, the
same shim calls `TriggerCapture()` instead.

## Chrome Probe

Evidence:
`build/renderdoc/chrome-gpu-delay-trigger-state-vulkan-only/html/evidence.env`.

Key result:

```text
rdoc_gpu_delay_trigger_loaded_count=1
rdoc_gpu_delay_trigger_api_ready_count=1
rdoc_gpu_delay_trigger_last_end_ok=0
rdoc_gpu_delay_trigger_elf_status=rdoc_delay_trigger_elf=symbol-found
rdoc_gpu_delay_trigger_capfile_template=/home/yoon/simple/build/renderdoc/chrome-gpu-delay-trigger-state-vulkan-only/html/gpu_chrome
rdoc_gpu_delay_trigger_num_captures_before=0
rdoc_gpu_delay_trigger_num_captures_after=0
rdoc_gpu_delay_trigger_is_capturing_after_start=0
rdoc_gpu_delay_trigger_is_capturing_before_end=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
rdoc_capture_magic=
```

The longer Chrome timing probe at
`build/renderdoc/chrome-gpu-delay-trigger-late-vulkan-only/html/evidence.env`
also reached the API and returned `EndFrameCapture ok=0`.

TriggerCapture evidence:
`build/renderdoc/chrome-gpu-triggercapture-vulkan-only/html/evidence.env`.

```text
rdoc_gpu_delay_trigger_loaded_count=1
rdoc_gpu_delay_trigger_api_ready_count=1
rdoc_gpu_delay_trigger_mode=trigger
rdoc_gpu_delay_trigger_capture_count=1
rdoc_gpu_delay_trigger_elf_status=rdoc_delay_trigger_elf=symbol-found
rdoc_gpu_delay_trigger_capfile_template=/home/yoon/simple/build/renderdoc/chrome-gpu-triggercapture-vulkan-only/html/gpu_chrome
rdoc_gpu_delay_trigger_num_captures_before=0
rdoc_gpu_delay_trigger_num_captures_after=0
rdoc_gpu_delay_trigger_is_capturing_after_trigger=0
rdoc_gpu_delay_trigger_is_capturing_before_end=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
rdoc_capture_magic=
```

Targeted-device evidence:
`build/renderdoc/chrome-gpu-delay-device-target-vulkan-only/html/evidence.env`.

```text
rdoc_gpu_delay_trigger_mode=start-end
rdoc_gpu_delay_trigger_target_device=(nil)
rdoc_gpu_delay_trigger_last_vk_instance=(nil)
rdoc_gpu_delay_trigger_vk_create_instance_count=0
rdoc_gpu_delay_trigger_last_end_ok=0
rdoc_gpu_delay_trigger_num_captures_after=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

## Electron Probe

Evidence:
`build/renderdoc/electron-gpu-delay-trigger-state-vulkan-only/electron-html/evidence.env`.

Key result:

```text
rdoc_gpu_delay_trigger_loaded_count=1
rdoc_gpu_delay_trigger_api_ready_count=1
rdoc_gpu_delay_trigger_last_end_ok=0
rdoc_gpu_delay_trigger_elf_status=rdoc_delay_trigger_elf=symbol-found
rdoc_gpu_delay_trigger_capfile_template=/home/yoon/simple/build/renderdoc/electron-gpu-delay-trigger-state-vulkan-only/electron-html/electron_gpu
rdoc_gpu_delay_trigger_num_captures_before=0
rdoc_gpu_delay_trigger_num_captures_after=0
rdoc_gpu_delay_trigger_is_capturing_after_start=0
rdoc_gpu_delay_trigger_is_capturing_before_end=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
rdoc_capture_magic=
```

TriggerCapture evidence:
`build/renderdoc/electron-gpu-triggercapture-vulkan-only/electron-html/evidence.env`.

```text
rdoc_gpu_delay_trigger_loaded_count=1
rdoc_gpu_delay_trigger_api_ready_count=1
rdoc_gpu_delay_trigger_mode=trigger
rdoc_gpu_delay_trigger_capture_count=1
rdoc_gpu_delay_trigger_elf_status=rdoc_delay_trigger_elf=symbol-found
rdoc_gpu_delay_trigger_capfile_template=/home/yoon/simple/build/renderdoc/electron-gpu-triggercapture-vulkan-only/electron-html/electron_gpu
rdoc_gpu_delay_trigger_num_captures_before=0
rdoc_gpu_delay_trigger_num_captures_after=0
rdoc_gpu_delay_trigger_is_capturing_after_trigger=0
rdoc_gpu_delay_trigger_is_capturing_before_end=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
rdoc_capture_magic=
```

Targeted-device evidence:
`build/renderdoc/electron-gpu-delay-device-target-vulkan-only/electron-html/evidence.env`.

```text
rdoc_gpu_delay_trigger_mode=start-end
rdoc_gpu_delay_trigger_target_device=(nil)
rdoc_gpu_delay_trigger_last_vk_instance=(nil)
rdoc_gpu_delay_trigger_vk_create_instance_count=0
rdoc_gpu_delay_trigger_last_end_ok=0
rdoc_gpu_delay_trigger_num_captures_after=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

## Aggregate

Focused aggregate:
`build/linux-vulkan-render-log-compare/evidence.env`.

The Linux aggregate now forwards:

```text
linux_vulkan_render_log_compare_renderdoc_chrome_delay_trigger_loaded_count=1
linux_vulkan_render_log_compare_renderdoc_chrome_delay_trigger_api_ready_count=1
linux_vulkan_render_log_compare_renderdoc_chrome_delay_trigger_mode=start-end
linux_vulkan_render_log_compare_renderdoc_chrome_delay_trigger_capture_count=0
linux_vulkan_render_log_compare_renderdoc_chrome_delay_trigger_last_end_ok=0
linux_vulkan_render_log_compare_renderdoc_chrome_delay_trigger_target_device=(nil)
linux_vulkan_render_log_compare_renderdoc_chrome_delay_trigger_last_vk_instance=(nil)
linux_vulkan_render_log_compare_renderdoc_chrome_delay_trigger_vk_create_instance_count=0
linux_vulkan_render_log_compare_renderdoc_chrome_delay_trigger_num_captures_after=0
linux_vulkan_render_log_compare_renderdoc_chrome_delay_trigger_is_capturing_after_start=0
linux_vulkan_render_log_compare_renderdoc_electron_delay_trigger_loaded_count=1
linux_vulkan_render_log_compare_renderdoc_electron_delay_trigger_api_ready_count=1
linux_vulkan_render_log_compare_renderdoc_electron_delay_trigger_mode=start-end
linux_vulkan_render_log_compare_renderdoc_electron_delay_trigger_capture_count=0
linux_vulkan_render_log_compare_renderdoc_electron_delay_trigger_last_end_ok=0
linux_vulkan_render_log_compare_renderdoc_electron_delay_trigger_target_device=(nil)
linux_vulkan_render_log_compare_renderdoc_electron_delay_trigger_last_vk_instance=(nil)
linux_vulkan_render_log_compare_renderdoc_electron_delay_trigger_vk_create_instance_count=0
linux_vulkan_render_log_compare_renderdoc_electron_delay_trigger_num_captures_after=0
linux_vulkan_render_log_compare_renderdoc_electron_delay_trigger_is_capturing_after_start=0
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
child using the Vulkan-only RenderDoc build. RenderDoc still declines both
trigger paths: the capfile template is set, but `IsFrameCapturing()` remains
`0` immediately after `StartFrameCapture`, `EndFrameCapture` returns `0`,
`TriggerCapture()` leaves `IsFrameCapturing()` at `0`, and `GetNumCaptures()`
remains `0`. A follow-up targeted-device probe added minimal
`vkCreateInstance`/`vkGetInstanceProcAddr` interception to derive
`RENDERDOC_DEVICEPOINTER_FROM_VKINSTANCE`, but Chromium/ANGLE does not route
instance creation through that LD_PRELOAD symbol path in either Chrome or
Electron (`vk_create_instance_count=0`, target device `(nil)`). The next
debugging target is inside the active RenderDoc Vulkan layer or target-control
state, not another `NULL,NULL` in-application API trigger.
