# RenderDoc Browser EGL Initialize Return Evidence - 2026-06-29

## Change

The browser GPU-process autocapture shim now records whether `eglInitialize`
returns after entry:

- `rdoc_gpu_autocapture_egl_initialize_return_count`
- `rdoc_gpu_autocapture_egl_initialize_success_count`
- `rdoc_gpu_autocapture_egl_initialize_fail_count`
- `rdoc_gpu_autocapture_egl_initialize_last_result`
- `rdoc_gpu_autocapture_egl_initialize_last_error`

The Linux render-log aggregate and GUI RenderDoc feature-coverage status forward
the same Chrome/Electron fields under
`linux_vulkan_render_log_compare_renderdoc_*`.

## Chrome Probe

Evidence file:
`build/renderdoc/chrome-gpu-egl-init-return/html/evidence.env`.

Key result:

```text
rdoc_chromium_gpu_launcher_angle_status=pass
rdoc_gpu_autocapture_egl_get_platform_display_count=1
rdoc_gpu_autocapture_egl_initialize_count=1
rdoc_gpu_autocapture_egl_initialize_return_count=0
rdoc_gpu_autocapture_egl_initialize_success_count=0
rdoc_gpu_autocapture_egl_initialize_fail_count=0
rdoc_gpu_autocapture_egl_initialize_last_result=-1
rdoc_gpu_autocapture_egl_initialize_last_error=-1
rdoc_gpu_autocapture_egl_choose_config_count=0
rdoc_gpu_autocapture_vk_enum_instance_layer_count=2
rdoc_gpu_autocapture_vk_create_instance_count=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

## Electron Probe

Evidence file:
`build/renderdoc/electron-gpu-egl-init-return/electron-html/evidence.env`.

Key result:

```text
rdoc_chromium_gpu_launcher_angle_status=pass
rdoc_gpu_autocapture_egl_get_platform_display_count=1
rdoc_gpu_autocapture_egl_initialize_count=1
rdoc_gpu_autocapture_egl_initialize_return_count=0
rdoc_gpu_autocapture_egl_initialize_success_count=0
rdoc_gpu_autocapture_egl_initialize_fail_count=0
rdoc_gpu_autocapture_egl_initialize_last_result=-1
rdoc_gpu_autocapture_egl_initialize_last_error=-1
rdoc_gpu_autocapture_egl_choose_config_count=0
rdoc_gpu_autocapture_vk_enum_instance_layer_count=2
rdoc_gpu_autocapture_vk_create_instance_count=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

## Aggregate

Focused aggregate:
`build/linux-vulkan-render-log-compare/evidence.env`.

Both Chrome and Electron keep `renderdoc-*-rdc` blocked with `missing-rdc`.
The forwarded fields show `egl_initialize_count=1` and
`egl_initialize_return_count=0` for both browser routes.

## Interpretation

The live Linux browser RenderDoc blocker is no longer only between EGL init and
config selection. Both browser GPU children enter `eglInitialize` under the
RenderDoc shim and do not return from that call before the run times out without
an `.rdc`. The next diagnostic should trace inside the EGL/ANGLE loader boundary
or compare the same `eglInitialize` call with RenderDoc layer/preload pieces
disabled one at a time.
