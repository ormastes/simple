# RenderDoc Browser GPU Launcher ANGLE Log Evidence - 2026-06-29

## Change

`scripts/tool/renderdoc-gpu-launcher.shs` now redirects GPU-child stdout/stderr
into `gpu-launcher.log` for layer-only and autocapture modes. The evidence
helper also emits a second ANGLE/EGL metadata set from that child log:

- `rdoc_chromium_gpu_launcher_angle_log`
- `rdoc_chromium_gpu_launcher_angle_status`
- `rdoc_chromium_gpu_launcher_angle_error_count`
- `rdoc_chromium_gpu_launcher_angle_first_error`
- `rdoc_chromium_gpu_launcher_angle_gpu_init_exit_count`

## Chrome Probe

Evidence file:
`build/renderdoc/chrome-gpu-launcher-angle-log/html/evidence.env`.

Key result:

```text
rdoc_chromium_angle_status=missing-log
rdoc_chromium_gpu_launcher_angle_status=pass
rdoc_chromium_gpu_launcher_angle_error_count=0
rdoc_chromium_gpu_launcher_angle_gpu_init_exit_count=0
rdoc_gpu_autocapture_vk_enum_instance_layer_count=2
rdoc_gpu_autocapture_vk_enum_instance_extension_count=1
rdoc_gpu_autocapture_vk_create_instance_count=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

## Electron Probe

Evidence file:
`build/renderdoc/electron-gpu-launcher-angle-log/electron-html/evidence.env`.

Key result:

```text
rdoc_chromium_angle_status=pass
rdoc_chromium_gpu_launcher_angle_status=pass
rdoc_chromium_gpu_launcher_angle_error_count=0
rdoc_chromium_gpu_launcher_angle_gpu_init_exit_count=0
rdoc_gpu_autocapture_vk_enum_instance_layer_count=2
rdoc_gpu_autocapture_vk_enum_instance_extension_count=1
rdoc_gpu_autocapture_vk_create_instance_count=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

## Interpretation

The Chrome app-mode main log is still absent, but the GPU child log is now
captured and parsed. Both Chrome and Electron GPU-child logs are free of visible
ANGLE/EGL initialization errors in this route. The remaining failure is still
before Vulkan instance creation: the browser process enumerates instance layers
and extensions, then never reaches `vkCreateInstance` before timeout.
