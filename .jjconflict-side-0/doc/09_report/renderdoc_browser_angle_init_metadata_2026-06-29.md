# RenderDoc Browser ANGLE Init Metadata - 2026-06-29

## Change

`scripts/lib/renderdoc-evidence-common.shs` now emits structured Chromium
ANGLE/EGL initialization metadata from the browser run log:

- `rdoc_chromium_angle_log`
- `rdoc_chromium_angle_status`
- `rdoc_chromium_angle_error_count`
- `rdoc_chromium_angle_first_error`
- `rdoc_chromium_angle_gpu_init_exit_count`

The scanner looks for ANGLE display initialization failures, EGL initialization
failures, `GLDisplayEGL::Initialize failed`, internal Vulkan errors, and GPU
process exits due to initialization errors.

## Chrome Probe

Evidence file:
`build/renderdoc/chrome-gpu-angle-init-current/html/evidence.env`.

Current Chrome app-mode GPU-launcher evidence reports:

```text
rdoc_chromium_angle_status=missing-log
rdoc_chromium_angle_error_count=0
rdoc_chromium_angle_gpu_init_exit_count=0
rdoc_gpu_autocapture_vk_enum_instance_layer_count=2
rdoc_gpu_autocapture_vk_enum_instance_extension_count=1
rdoc_gpu_autocapture_vk_create_instance_count=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

The Chrome app-mode launcher route does not leave a populated
`renderdoc-html.log`, so ANGLE errors cannot be read from that log in this
mode. The GPU launcher evidence remains available through `gpu-launcher.log`.

## Electron Probe

Evidence file:
`build/renderdoc/electron-gpu-angle-init-current/electron-html/evidence.env`.

Current Electron visible-window GPU-launcher evidence reports:

```text
rdoc_chromium_angle_status=pass
rdoc_chromium_angle_error_count=0
rdoc_chromium_angle_gpu_init_exit_count=0
rdoc_gpu_autocapture_vk_enum_instance_layer_count=2
rdoc_gpu_autocapture_vk_enum_instance_extension_count=1
rdoc_gpu_autocapture_vk_create_instance_count=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

## Interpretation

After the shim resolver fix, the current Electron route does not expose an
ANGLE/EGL initialization error in the wrapper log. Both browser routes still
reach Vulkan layer and extension enumeration but do not reach Vulkan instance
creation before timeout, so the remaining blocker is still between
enumeration and `vkCreateInstance`, not a visible post-instance frame capture
failure.
