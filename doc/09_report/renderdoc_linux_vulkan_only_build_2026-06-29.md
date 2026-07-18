# Linux Vulkan-Only RenderDoc Build Evidence - 2026-06-29

## Build Path

Added wrapper:
`scripts/setup/build-renderdoc-linux-vulkan-only.shs`.

The wrapper builds RenderDoc `v1.44` under `build/tools/` with:

```text
-DENABLE_GL=OFF
-DENABLE_GLES=OFF
-DENABLE_EGL=OFF
-DENABLE_VULKAN=ON
-DENABLE_QRENDERDOC=OFF
-DENABLE_PYRENDERDOC=OFF
-DVULKAN_LAYER_FOLDER=build/tools/renderdoc-linux-vulkan-only/etc/vulkan/implicit_layer.d
```

Installed tree:
`build/tools/renderdoc-linux-vulkan-only`.

`renderdoccmd --version` reports:

```text
renderdoccmd x64 v1.44 built from 050034a0faa37d606ce1b8cf677dba4bc36984ea
APIs supported at compile-time: Vulkan.
Windowing systems supported at compile-time: xlib, XCB, Vulkan KHR_display.
```

The shared RenderDoc helper now prefers this tree on Linux when it exists, so
browser capture diagnostics do not silently fall back to the distro/package
RenderDoc build.

## Host Setup

Installed Ubuntu build prerequisites for this host included:

```text
cmake
ninja-build
python3-dev
pkg-config
libvulkan-dev
libx11-dev
libx11-xcb-dev
libxcb*-dev
libxkbcommon-dev
libxkbcommon-x11-dev
```

Wrapper check evidence:
`build/tools/renderdoc-linux-vulkan-only-build/evidence.env`.

Key result:

```text
renderdoc_vulkan_only_renderdoccmd_status=pass
renderdoc_vulkan_only_layer_manifest_status=pass
renderdoc_vulkan_only_rdoc_home=/home/yoon/simple/build/tools/renderdoc-linux-vulkan-only
```

## Browser Probe Result

Chrome evidence:
`build/renderdoc/chrome-gpu-vulkan-only-renderdoc/html/evidence.env`.

Electron evidence:
`build/renderdoc/electron-gpu-vulkan-only-renderdoc/electron-html/evidence.env`.

Both browser routes still report:

```text
rdoc_gpu_autocapture_egl_initialize_count=1
rdoc_gpu_autocapture_egl_initialize_return_count=0
rdoc_gpu_autocapture_egl_choose_config_count=0
rdoc_gpu_autocapture_vk_enum_instance_layer_count=2
rdoc_gpu_autocapture_vk_create_instance_count=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

Focused aggregate:
`build/linux-vulkan-render-log-compare/evidence.env`.

The aggregate still keeps `renderdoc-chrome-rdc` and
`renderdoc-electron-rdc` blocked.

## Interpretation

The no-GL/GLES RenderDoc build path is now reproducible and selected by the
repo helpers, but it is not sufficient on this host. The remaining browser
blocker is still inside Chromium/ANGLE `eglInitialize` before Vulkan instance
creation and before any RenderDoc `.rdc` artifact appears.
