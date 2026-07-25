# RenderDoc Linux Aggregate Browser Fields - 2026-06-29

## Change

`scripts/check/check-linux-vulkan-render-log-compare.shs` now promotes current
browser GPU-launcher diagnostics from Chrome and Electron RenderDoc evidence
into the Linux aggregate env.

Forwarded Chrome fields include:

- `linux_vulkan_render_log_compare_renderdoc_chrome_gpu_launcher_angle_status`
- `linux_vulkan_render_log_compare_renderdoc_chrome_gpu_launcher_angle_error_count`
- `linux_vulkan_render_log_compare_renderdoc_chrome_gpu_launcher_clear_renderdoc_layer`
- `linux_vulkan_render_log_compare_renderdoc_chrome_gpu_launcher_vk_instance_layers`
- `linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_status`
- `linux_vulkan_render_log_compare_renderdoc_chrome_vk_enum_instance_layer_count`
- `linux_vulkan_render_log_compare_renderdoc_chrome_vk_enum_instance_extension_count`
- `linux_vulkan_render_log_compare_renderdoc_chrome_vk_create_instance_count`
- `linux_vulkan_render_log_compare_renderdoc_chrome_vk_create_device_count`

The Electron fields use the same suffixes under
`linux_vulkan_render_log_compare_renderdoc_electron_*`.

`scripts/check/check-gui-renderdoc-feature-coverage-status.shs` now passes
these fields through to the broader feature-coverage status output.

## Evidence

Focused Linux compare run:

```bash
RDOC_HTML_EVIDENCE_ENV=build/renderdoc/chrome-gpu-launcher-angle-log/html/evidence.env \
RDOC_ELECTRON_HTML_EVIDENCE_ENV=build/renderdoc/electron-gpu-launcher-angle-log/electron-html/evidence.env \
BUILD_DIR=build/linux-vulkan-render-log-compare \
sh scripts/check/check-linux-vulkan-render-log-compare.shs
```

Relevant aggregate output:

```text
linux_vulkan_render_log_compare_blocked_gates=simple-vulkan-backend,pairwise-argb-diff,argb-source-evidence,renderdoc-chrome-rdc,renderdoc-electron-rdc
linux_vulkan_render_log_compare_renderdoc_chrome_reason=missing-rdc
linux_vulkan_render_log_compare_renderdoc_chrome_gpu_launcher_angle_status=pass
linux_vulkan_render_log_compare_renderdoc_chrome_vk_enum_instance_layer_count=2
linux_vulkan_render_log_compare_renderdoc_chrome_vk_create_instance_count=0
linux_vulkan_render_log_compare_renderdoc_electron_reason=missing-rdc
linux_vulkan_render_log_compare_renderdoc_electron_gpu_launcher_angle_status=pass
linux_vulkan_render_log_compare_renderdoc_electron_vk_enum_instance_layer_count=2
linux_vulkan_render_log_compare_renderdoc_electron_vk_create_instance_count=0
```

The broader feature-coverage status script emits the same forwarded fields.

## Interpretation

Linux GUI/Web aggregate verification can now preserve the current browser
RenderDoc failure classification: Chrome and Electron keep
`renderdoc-chrome-rdc` and `renderdoc-electron-rdc` blocked, with GPU-launcher
ANGLE status passing and Vulkan layer enumeration reached, but no
`vkCreateInstance` before timeout.
