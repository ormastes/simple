# RenderDoc Browser GPU Launcher Boundary Evidence - 2026-06-29

## Change

The GPU launcher now writes the GPU child command boundary into
`gpu-launcher.log`, and the RenderDoc evidence parser promotes those values to
`evidence.env`.

New structured fields include:

- `rdoc_gpu_launcher_command`
- `rdoc_gpu_launcher_executable`
- `rdoc_gpu_launcher_argc`
- `rdoc_gpu_launcher_ld_preload`
- `rdoc_gpu_launcher_ld_library_path`
- `rdoc_gpu_launcher_vk_layer_path`
- `rdoc_gpu_launcher_vk_instance_layers`
- `rdoc_gpu_launcher_enable_vulkan_renderdoc_capture`
- `rdoc_gpu_launcher_renderdoc_capfile`
- `rdoc_gpu_launcher_shim`
- `rdoc_gpu_launcher_renderdoc_lib`

The autocapture shim also wraps the EGL lifecycle symbols through `dlsym`, not
only `eglGetProcAddress`.

## Chrome Probe

Evidence file:
`build/renderdoc/chrome-gpu-launcher-boundary-current/html/evidence.env`.

Key result:

```text
rdoc_gpu_launcher_executable=/opt/google/chrome/chrome
rdoc_gpu_launcher_argc=20
rdoc_gpu_launcher_vk_instance_layers=VK_LAYER_RENDERDOC_Capture
rdoc_gpu_launcher_enable_vulkan_renderdoc_capture=1
rdoc_gpu_launcher_ld_preload=/home/yoon/simple/build/renderdoc/autocapture-shim/renderdoc-vulkan-autocapture.so
rdoc_gpu_autocapture_loaded_count=1
rdoc_gpu_autocapture_status=not-started
rdoc_gpu_autocapture_proc_trace_count=220
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

## Electron Probe

Evidence file:
`build/renderdoc/electron-gpu-launcher-boundary-current/electron-html/evidence.env`.

Key result:

```text
rdoc_gpu_launcher_executable=/home/yoon/simple/tools/electron-shell/node_modules/electron/dist/electron
rdoc_gpu_launcher_argc=18
rdoc_gpu_launcher_vk_instance_layers=VK_LAYER_RENDERDOC_Capture
rdoc_gpu_launcher_enable_vulkan_renderdoc_capture=1
rdoc_gpu_launcher_ld_preload=/home/yoon/simple/build/renderdoc/autocapture-shim/renderdoc-vulkan-autocapture.so
rdoc_gpu_autocapture_loaded_count=1
rdoc_gpu_autocapture_status=not-started
rdoc_gpu_autocapture_proc_trace_count=220
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

## Interpretation

The failing browser RenderDoc route is no longer explained by a missing GPU
launcher invocation, missing Vulkan layer environment, missing RenderDoc capture
enable flag, missing capfile, missing `LD_PRELOAD`, or missing shim load. Both
Chrome and Electron start a GPU child with Vulkan/ANGLE flags and the expected
RenderDoc environment, and the preload constructor runs in that child.

The active route still does not call the wrapped Vulkan queue, EGL swap, ANGLE
scheduling, or EGL lifecycle symbols before timeout. The next useful diagnostic
should inspect Vulkan loader/layer dispatch inside the GPU child or RenderDoc
layer registration rather than adding more frame/surface hooks.
