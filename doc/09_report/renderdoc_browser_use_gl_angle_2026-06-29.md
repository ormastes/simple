# Browser RenderDoc `--use-gl=angle` Probe

Status: fail
Date: 2026-06-29

## Summary

Chrome and Electron were rerun through the GPU-child RenderDoc autocapture path
with the opt-in Chromium flag `--use-gl=angle` appended to the existing Vulkan
launch flags. This does not close the Linux browser `.rdc` gate.

The GPU child still loads the autocapture shim, keeps
`VK_LAYER_RENDERDOC_Capture` active, reports no ANGLE initialization errors, and
then enters `eglInitialize` without returning before timeout. Both browser
routes remain before `eglChooseConfig`, `vkCreateInstance`, and
`vkCreateDevice`, so no `RDOC` capture artifact is produced.

## Evidence

Chrome:

- evidence: `build/renderdoc/chrome-gpu-use-gl-angle/html/evidence.env`
- launch flag: `--use-gl=angle`
- `rdoc_chromium_gpu_launcher_angle_status=pass`
- `rdoc_gpu_autocapture_egl_get_platform_display_count=1`
- `rdoc_gpu_autocapture_egl_initialize_count=1`
- `rdoc_gpu_autocapture_egl_initialize_return_count=0`
- `rdoc_gpu_autocapture_egl_choose_config_count=0`
- `rdoc_gpu_autocapture_vk_create_instance_count=0`
- `rdoc_capture_status=fail`
- `rdoc_capture_reason=missing-rdc`

Electron:

- evidence: `build/renderdoc/electron-gpu-use-gl-angle/electron-html/evidence.env`
- launch flag: `--use-gl=angle`
- `rdoc_chromium_gpu_launcher_angle_status=pass`
- `rdoc_gpu_autocapture_egl_get_platform_display_count=1`
- `rdoc_gpu_autocapture_egl_initialize_count=1`
- `rdoc_gpu_autocapture_egl_initialize_return_count=0`
- `rdoc_gpu_autocapture_egl_choose_config_count=0`
- `rdoc_gpu_autocapture_vk_create_instance_count=0`
- `rdoc_capture_status=fail`
- `rdoc_capture_reason=missing-rdc`

## Command Shape

The shared flag helpers now accept diagnostic-only extra flags without changing
the canonical defaults:

```sh
RDOC_CHROME_EXTRA_VULKAN_FLAGS='--use-gl=angle' \
  scripts/tool/renderdoc-evidence.shs capture-html

RDOC_ELECTRON_EXTRA_VULKAN_FLAGS='--use-gl=angle' \
  scripts/tool/renderdoc-evidence.shs capture-electron-html
```

This is a diagnostic path, not passing evidence.
