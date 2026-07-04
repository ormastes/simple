# Browser RenderDoc Implicit-Layer Capture

Status: pass
Date: 2026-06-29

## Summary

Chrome and Electron browser RenderDoc capture now pass on Linux when the GPU
child uses the per-run Vulkan-only RenderDoc implicit layer manifest.

The earlier failing runs exported `VK_LAYER_PATH`, but the Vulkan loader could
still select the globally registered `/opt/renderdoc` implicit layer. GDB stack
evidence showed the GPU child opening the system RenderDoc library while inside
the Vulkan loader and then calling back through Chromium `eglGetProcAddress`,
which left the process blocked before `vkCreateInstance`.

The capture helpers now also export `VK_IMPLICIT_LAYER_PATH` to the generated
run-local `vulkan-layer.d` directory. With that path forced, both browser GPU
children return from `eglInitialize`, reach `vkCreateInstance` and
`vkCreateDevice`, start/end RenderDoc capture from Vulkan submit hooks, and
write valid `.rdc` artifacts with `RDOC` magic.

## Passing Evidence

Chrome:

- evidence: `build/renderdoc/chrome-implicit-layer-default-autocapture/html/evidence.env`
- gate: `build/renderdoc/chrome-implicit-layer-default-gate/evidence.env`
- capture: `build/renderdoc/chrome-implicit-layer-default-autocapture/html/gpu_chrome_capture.rdc`
- `rdoc_capture_status=pass`
- `rdoc_capture_magic=RDOC`
- `rdoc_gpu_launcher_vk_implicit_layer_path=/home/yoon/simple/build/renderdoc/chrome-implicit-layer-default-autocapture/html/vulkan-layer.d`
- `rdoc_gpu_autocapture_status=ended`
- `rdoc_gpu_autocapture_api=1`
- `rdoc_gpu_autocapture_vk_create_instance_count=1`
- `rdoc_gpu_autocapture_vk_create_device_count=1`

Electron:

- evidence: `build/renderdoc/electron-implicit-layer-default-autocapture/electron-html/evidence.env`
- gate: `build/renderdoc/electron-implicit-layer-default-gate/evidence.env`
- capture: `build/renderdoc/electron-implicit-layer-default-autocapture/electron-html/electron_gpu_capture.rdc`
- `rdoc_capture_status=pass`
- `rdoc_capture_magic=RDOC`
- `rdoc_electron_html_gate_status=pass`
- `rdoc_gpu_launcher_vk_implicit_layer_path=/home/yoon/simple/build/renderdoc/electron-implicit-layer-default-autocapture/electron-html/vulkan-layer.d`
- `rdoc_gpu_autocapture_status=ended`
- `rdoc_gpu_autocapture_api=1`
- `rdoc_gpu_autocapture_vk_create_instance_count=1`
- `rdoc_gpu_autocapture_vk_create_device_count=1`

Linux aggregate:

- evidence: `build/linux-vulkan-render-log-compare-implicit-layer-default-raw/evidence.env`
- `linux_vulkan_render_log_compare_renderdoc_gate_status=pass`
- `linux_vulkan_render_log_compare_renderdoc_chrome_status=pass`
- `linux_vulkan_render_log_compare_renderdoc_chrome_artifact_magic=RDOC`
- `linux_vulkan_render_log_compare_renderdoc_electron_status=pass`
- `linux_vulkan_render_log_compare_renderdoc_electron_artifact_magic=RDOC`

The aggregate still reports non-RenderDoc blockers for Simple Vulkan status
metadata and pairwise ARGB source evidence. Those are separate from the browser
`.rdc` gate.
