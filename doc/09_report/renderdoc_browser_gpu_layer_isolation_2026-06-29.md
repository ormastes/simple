# RenderDoc Browser GPU Layer Isolation Evidence - 2026-06-29

## Purpose

After the browser GPU-child autocapture shim proved that Chrome and Electron
enter `eglInitialize` but do not return while the RenderDoc Vulkan layer is
present, this run used existing launcher switches to isolate layer, preload
shim, and layer-only behavior.

## Layer Present With Autocapture Shim

Evidence:

- `build/renderdoc/chrome-gpu-egl-init-return/html/evidence.env`
- `build/renderdoc/electron-gpu-egl-init-return/electron-html/evidence.env`

Both browser routes report:

```text
rdoc_gpu_autocapture_egl_initialize_count=1
rdoc_gpu_autocapture_egl_initialize_return_count=0
rdoc_gpu_autocapture_egl_choose_config_count=0
rdoc_gpu_autocapture_vk_enum_instance_layer_count=2
rdoc_gpu_autocapture_vk_create_instance_count=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

## Layer Cleared With Autocapture Shim

Chrome command used `RDOC_GPU_LAUNCHER_CLEAR_RENDERDOC_LAYER=1` with
`RDOC_CHROME_GPU_AUTOCAPTURE=1`.

Evidence:
`build/renderdoc/chrome-gpu-egl-init-return-no-layer/html/evidence.env`.

Key result:

```text
rdoc_chromium_gpu_process_exit_status=fail
rdoc_chromium_gpu_process_exit_codes=139
rdoc_gpu_launcher_clear_renderdoc_layer=1
rdoc_gpu_autocapture_egl_initialize_count=0
rdoc_gpu_autocapture_vk_enum_instance_layer_count=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

Electron command used `RDOC_GPU_LAUNCHER_CLEAR_RENDERDOC_LAYER=1` with
`RDOC_ELECTRON_GPU_AUTOCAPTURE=1`.

Evidence:
`build/renderdoc/electron-gpu-egl-init-return-no-layer/electron-html/evidence.env`.

Key result:

```text
rdoc_chromium_gpu_process_exit_status=fail
rdoc_chromium_gpu_process_exit_codes=139
rdoc_gpu_launcher_clear_renderdoc_layer=1
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

## Layer Only Without Autocapture Shim

Chrome command used `RDOC_CHROME_GPU_LAUNCHER=1` and
`RDOC_GPU_LAUNCHER_LAYER_ONLY=1`.

Evidence:
`build/renderdoc/chrome-gpu-layer-only/html/evidence.env`.

Key result:

```text
rdoc_chrome_display_mode=gpu-launcher
rdoc_gpu_autocapture_status=missing-summary
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

Electron command used `RDOC_ELECTRON_GPU_LAUNCHER=1` and
`RDOC_GPU_LAUNCHER_LAYER_ONLY=1`.

Evidence:
`build/renderdoc/electron-gpu-layer-only/electron-html/evidence.env`.

Key result:

```text
rdoc_electron_display_mode=gpu-launcher
rdoc_chromium_gpu_process_exit_status=pass
rdoc_gpu_autocapture_status=missing-summary
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

## Interpretation

The Linux browser RenderDoc blocker has three distinct behaviors:

- RenderDoc layer plus shim: Chrome and Electron enter `eglInitialize` but do
  not return before `.rdc` remains missing.
- Shim with RenderDoc layer cleared: Chrome and Electron GPU children crash with
  `exit_code=139` before useful EGL/Vulkan wrapper telemetry.
- RenderDoc layer only without the shim: Chrome and Electron do not emit `.rdc`;
  the shim summary is absent by design.

None of these modes is passing browser RenderDoc evidence. The next fix should
focus on the RenderDoc layer/ANGLE `eglInitialize` interaction or use a
different browser-GPU capture route that still produces a valid `RDOC` artifact.
