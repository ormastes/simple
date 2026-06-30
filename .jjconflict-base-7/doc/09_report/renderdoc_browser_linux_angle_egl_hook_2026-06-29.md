# RenderDoc Browser Linux ANGLE EGL Hook Evidence - 2026-06-29

## Upstream Constraint

ANGLE's debugging guide documents that RenderDoc can hook EGL entry points and
capture Chromium's app-facing EGL calls rather than ANGLE's backend Vulkan work.
It lists `RENDERDOC_HOOK_EGL=0` as a Windows workaround and says Linux has no
equivalent supported workaround except building RenderDoc without GL/GLES
support.

Reference:
`https://chromium.googlesource.com/angle/angle/+/main/doc/DebuggingTips.md`

## Local Probe

The local installed RenderDoc path was tested with `RENDERDOC_HOOK_EGL=0` on
both browser GPU-process autocapture routes.

Chrome evidence:
`build/renderdoc/chrome-gpu-egl-hook-off/html/evidence.env`.

```text
rdoc_gpu_autocapture_egl_initialize_count=1
rdoc_gpu_autocapture_egl_initialize_return_count=0
rdoc_gpu_autocapture_egl_choose_config_count=0
rdoc_gpu_autocapture_vk_enum_instance_layer_count=2
rdoc_gpu_autocapture_vk_create_instance_count=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

Electron evidence:
`build/renderdoc/electron-gpu-egl-hook-off/electron-html/evidence.env`.

```text
rdoc_gpu_autocapture_egl_initialize_count=1
rdoc_gpu_autocapture_egl_initialize_return_count=0
rdoc_gpu_autocapture_egl_choose_config_count=0
rdoc_gpu_autocapture_vk_enum_instance_layer_count=2
rdoc_gpu_autocapture_vk_create_instance_count=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

## Aggregate Classification

The Linux render-log compare aggregate now emits:

```text
linux_vulkan_render_log_compare_renderdoc_linux_angle_workaround_status=needed
linux_vulkan_render_log_compare_renderdoc_linux_angle_workaround_reason=linux-angle-eglinitialize-does-not-return-under-renderdoc-layer
```

This is a blocker classification only. It does not pass or weaken
`renderdoc-chrome-rdc` or `renderdoc-electron-rdc`; both still require real
`.rdc` artifacts with `RDOC` magic.

## Interpretation

The packaged Linux RenderDoc build does not honor `RENDERDOC_HOOK_EGL=0` in a
way that unblocks Chromium/ANGLE capture on this host. The next implementation
step should provide or select a Linux RenderDoc build without GL/GLES support,
then rerun the Chrome/Electron GPU-process `.rdc` gates against that build.
