# RenderDoc Browser GPU Autocapture EGL Lifecycle Evidence - 2026-06-29

## Change

The GPU-process autocapture shim now records passive lifecycle counters for:

- `eglMakeCurrent`
- `eglCreateWindowSurface`
- `eglCreatePlatformWindowSurface`

The structured evidence parser emits these fields:

- `rdoc_gpu_autocapture_egl_make_current_count`
- `rdoc_gpu_autocapture_egl_create_window_surface_count`
- `rdoc_gpu_autocapture_egl_create_platform_window_surface_count`

## Electron Probe

Command:

```bash
RDOC_OUTPUT_DIR=build/renderdoc/electron-gpu-autocapture-egl-lifecycle \
RDOC_ELECTRON_GPU_AUTOCAPTURE=1 \
RDOC_ELECTRON_SHOW_WINDOW=1 \
RDOC_AUTOCAPTURE_ALLOW_DLOPEN=1 \
RDOC_GPU_LAUNCHER_ALLOW_DLOPEN=1 \
RDOC_GPU_LAUNCHER_NO_DLOPEN_FALLBACK=1 \
RDOC_AUTOCAPTURE_TRACE_PROC_NAMES=1 \
RDOC_AUTOCAPTURE_TRACE_PROC_NAMES_MAX=220 \
RDOC_AUTOCAPTURE_SUMMARY_INTERVAL_MS=2000 \
RDOC_CAPTURE_TIMEOUT_SECS=20 \
scripts/tool/renderdoc-evidence.shs capture-electron-html
```

Result:

```text
rdoc_gpu_autocapture_status=not-started
rdoc_gpu_autocapture_api=0
rdoc_gpu_autocapture_proc_trace_count=220
rdoc_gpu_autocapture_egl_make_current_count=0
rdoc_gpu_autocapture_egl_create_window_surface_count=0
rdoc_gpu_autocapture_egl_create_platform_window_surface_count=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

Evidence:
`build/renderdoc/electron-gpu-autocapture-egl-lifecycle/electron-html/evidence.env`.

## Chrome Probe

Command:

```bash
RDOC_OUTPUT_DIR=build/renderdoc/chrome-gpu-autocapture-egl-lifecycle \
RDOC_CHROME_GPU_AUTOCAPTURE=1 \
RDOC_CHROME_APP_MODE=1 \
RDOC_AUTOCAPTURE_ALLOW_DLOPEN=1 \
RDOC_GPU_LAUNCHER_ALLOW_DLOPEN=1 \
RDOC_GPU_LAUNCHER_NO_DLOPEN_FALLBACK=1 \
RDOC_AUTOCAPTURE_TRACE_PROC_NAMES=1 \
RDOC_AUTOCAPTURE_TRACE_PROC_NAMES_MAX=220 \
RDOC_AUTOCAPTURE_SUMMARY_INTERVAL_MS=2000 \
RDOC_CAPTURE_TIMEOUT_SECS=20 \
scripts/tool/renderdoc-evidence.shs capture-html
```

Result:

```text
rdoc_gpu_autocapture_status=not-started
rdoc_gpu_autocapture_api=0
rdoc_gpu_autocapture_proc_trace_count=220
rdoc_gpu_autocapture_egl_make_current_count=0
rdoc_gpu_autocapture_egl_create_window_surface_count=0
rdoc_gpu_autocapture_egl_create_platform_window_surface_count=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
```

Evidence:
`build/renderdoc/chrome-gpu-autocapture-egl-lifecycle/html/evidence.env`.

## Interpretation

Both browser routes inject the shim and keep it alive long enough for heartbeat
summaries, but the active browser rendering path does not call the currently
wrapped Vulkan queue, EGL swap, ANGLE scheduling, or EGL lifecycle entry points.
The next useful diagnostic should move earlier than frame and surface calls,
for example toward Chromium GPU launcher ownership, Vulkan loader/layer
dispatch, or RenderDoc layer registration inside the child process.
