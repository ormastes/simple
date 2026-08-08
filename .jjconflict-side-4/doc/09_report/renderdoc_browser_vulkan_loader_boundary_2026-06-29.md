# RenderDoc Browser Vulkan Loader Boundary Evidence - 2026-06-29

## Change

The browser GPU-process autocapture shim now records Vulkan loader/layer
boundary counters:

- `vkEnumerateInstanceLayerProperties`
- `vkEnumerateInstanceExtensionProperties`
- `vkCreateInstance`
- `vkCreateDevice`

The shim resolver also falls back to the already-loaded `libvulkan` and
`libEGL` libraries when `RTLD_NEXT` cannot find the real symbol. Without this,
exported diagnostic wrappers can become intrusive and break ANGLE Vulkan
initialization before evidence is collected.

## Chrome Probe

Evidence file:
`build/renderdoc/chrome-gpu-vulkan-loader-boundary/html/evidence.env`.

Key result:

```text
rdoc_gpu_launcher_vk_instance_layers=VK_LAYER_RENDERDOC_Capture
rdoc_gpu_autocapture_loaded_count=1
rdoc_gpu_autocapture_proc_trace_count=260
rdoc_gpu_autocapture_vk_enum_instance_layer_count=2
rdoc_gpu_autocapture_vk_enum_instance_extension_count=1
rdoc_gpu_autocapture_vk_create_instance_count=0
rdoc_gpu_autocapture_vk_create_device_count=0
rdoc_gpu_autocapture_status=not-started
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

## Electron Probe

Evidence file:
`build/renderdoc/electron-gpu-vulkan-loader-boundary/electron-html/evidence.env`.

Key result:

```text
rdoc_gpu_launcher_vk_instance_layers=VK_LAYER_RENDERDOC_Capture
rdoc_gpu_autocapture_loaded_count=1
rdoc_gpu_autocapture_proc_trace_count=260
rdoc_gpu_autocapture_vk_enum_instance_layer_count=2
rdoc_gpu_autocapture_vk_enum_instance_extension_count=1
rdoc_gpu_autocapture_vk_create_instance_count=0
rdoc_gpu_autocapture_vk_create_device_count=0
rdoc_gpu_autocapture_status=not-started
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

## Interpretation

Both browser GPU-child routes reach Vulkan instance layer and extension
enumeration with the RenderDoc layer environment active. They do not proceed to
`vkCreateInstance` or `vkCreateDevice` before timeout, so no frame capture can
start and no `.rdc` is produced.

This shifts the remaining Linux browser RenderDoc blocker below launcher setup
and above frame submission: the GPU child sees the Vulkan loader boundary, but
Chromium/ANGLE does not create a Vulkan instance in this RenderDoc child route.
The next diagnostic should inspect ANGLE's layer/device selection result or the
RenderDoc layer's interaction with ANGLE before instance creation.
