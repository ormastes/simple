# RenderDoc Browser No-Layer Isolation Evidence - 2026-06-29

## Change

`scripts/tool/renderdoc-gpu-launcher.shs` now supports the diagnostic-only
switch `RDOC_GPU_LAUNCHER_CLEAR_RENDERDOC_LAYER=1`. In autocapture and
layer-only launcher modes, this clears `VK_INSTANCE_LAYERS` and
`ENABLE_VULKAN_RENDERDOC_CAPTURE` immediately before executing the Chromium GPU
child while preserving the preload shim.

The evidence parser emits:

```text
rdoc_gpu_launcher_clear_renderdoc_layer
```

This switch is not passing RenderDoc evidence because it disables the RenderDoc
Vulkan layer needed for browser `.rdc` capture.

## Chrome Probe

Evidence file:
`build/renderdoc/chrome-gpu-no-renderdoc-layer/html/evidence.env`.

Command classification:

```text
rdoc_gpu_launcher_clear_renderdoc_layer=1
rdoc_gpu_launcher_vk_instance_layers=
rdoc_gpu_launcher_enable_vulkan_renderdoc_capture=
rdoc_chromium_gpu_process_exit_status=fail
rdoc_chromium_gpu_process_exit_count=9
rdoc_chromium_gpu_process_exit_codes=139
rdoc_gpu_autocapture_loaded_count=10
rdoc_gpu_autocapture_status=not-started
rdoc_gpu_autocapture_vk_create_instance_count=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

## Electron Probe

Evidence file:
`build/renderdoc/electron-gpu-no-renderdoc-layer/electron-html/evidence.env`.

Command classification:

```text
rdoc_gpu_launcher_clear_renderdoc_layer=1
rdoc_gpu_launcher_vk_instance_layers=
rdoc_gpu_launcher_enable_vulkan_renderdoc_capture=
rdoc_chromium_gpu_process_exit_status=fail
rdoc_chromium_gpu_process_exit_count=6
rdoc_chromium_gpu_process_exit_codes=139
rdoc_gpu_autocapture_loaded_count=7
rdoc_gpu_autocapture_status=shim-loaded-no-summary
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

## Interpretation

The layer-enabled GPU-launcher route keeps the Chromium GPU child alive long
enough to emit heartbeat summaries and prove Vulkan layer/extension
enumeration, but it never reaches `vkCreateInstance`.

The layer-cleared route is not a workaround: both Chrome and Electron repeatedly
crash the GPU child with `exit_code=139` and still emit no `.rdc`. This keeps
the browser RenderDoc blocker in the RenderDoc/Chromium GPU-child interaction
lane rather than offering a no-layer capture path.
