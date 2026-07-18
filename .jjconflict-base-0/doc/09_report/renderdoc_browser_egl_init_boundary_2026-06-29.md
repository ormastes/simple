# RenderDoc Browser EGL Init Boundary Evidence - 2026-06-29

## Change

The browser GPU-process autocapture shim now records passive EGL display/init
boundary counters:

- `eglGetDisplay`
- `eglGetPlatformDisplay`
- `eglInitialize`
- `eglChooseConfig`

The evidence parser emits the corresponding
`rdoc_gpu_autocapture_egl_*_count` fields, and the Linux aggregate checks
forward the key EGL init counters for Chrome and Electron.

## Chrome Probe

Evidence file:
`build/renderdoc/chrome-gpu-egl-init-boundary/html/evidence.env`.

Key result:

```text
rdoc_chromium_gpu_launcher_angle_status=pass
rdoc_gpu_autocapture_egl_get_platform_display_count=1
rdoc_gpu_autocapture_egl_initialize_count=1
rdoc_gpu_autocapture_egl_choose_config_count=0
rdoc_gpu_autocapture_vk_enum_instance_layer_count=2
rdoc_gpu_autocapture_vk_create_instance_count=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

## Electron Probe

Evidence file:
`build/renderdoc/electron-gpu-egl-init-boundary/electron-html/evidence.env`.

Key result:

```text
rdoc_chromium_gpu_launcher_angle_status=pass
rdoc_gpu_autocapture_egl_get_platform_display_count=1
rdoc_gpu_autocapture_egl_initialize_count=1
rdoc_gpu_autocapture_egl_choose_config_count=0
rdoc_gpu_autocapture_vk_enum_instance_layer_count=2
rdoc_gpu_autocapture_vk_create_instance_count=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

## Interpretation

Both browser GPU-child routes enter EGL display selection and call
`eglInitialize` once. Neither route reaches `eglChooseConfig`, EGL surface
creation, frame submission, or Vulkan instance creation before timeout. The
remaining Linux browser RenderDoc blocker is now narrowed to after
`eglInitialize` and before EGL config selection / Vulkan instance creation.
