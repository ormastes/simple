# RenderDoc Electron GPU Autocapture Heartbeat Evidence - 2026-06-29

## Command

```bash
RDOC_OUTPUT_DIR=build/renderdoc/electron-gpu-autocapture-current \
RDOC_ELECTRON_GPU_AUTOCAPTURE=1 \
RDOC_ELECTRON_SHOW_WINDOW=1 \
RDOC_AUTOCAPTURE_ALLOW_DLOPEN=1 \
RDOC_GPU_LAUNCHER_ALLOW_DLOPEN=1 \
RDOC_GPU_LAUNCHER_NO_DLOPEN_FALLBACK=1 \
RDOC_AUTOCAPTURE_TRACE_PROC_NAMES=1 \
RDOC_AUTOCAPTURE_TRACE_PROC_NAMES_MAX=160 \
RDOC_AUTOCAPTURE_SUMMARY_INTERVAL_MS=2000 \
RDOC_CAPTURE_TIMEOUT_SECS=20 \
scripts/tool/renderdoc-evidence.shs capture-electron-html
```

## Result

Status: fail, `rdoc_capture_reason=missing-rdc`.

The Electron GPU launcher path loaded the autocapture shim and the process did
not report a Chromium GPU-process crash:

```text
rdoc_electron_display_mode=gpu-autocapture
rdoc_electron_launch_exit_code=124
rdoc_chromium_gpu_process_exit_count=0
rdoc_gpu_autocapture_loaded_count=1
rdoc_gpu_autocapture_proc_trace_line_count=160
```

The heartbeat summary proves the shim stayed alive until timeout, but none of
the currently wrapped frame trigger calls executed before timeout:

```text
rdoc_gpu_autocapture_status=not-started
rdoc_gpu_autocapture_api=0
rdoc_gpu_autocapture_submit_count=0
rdoc_gpu_autocapture_present_count=0
rdoc_gpu_autocapture_egl_swap_count=0
rdoc_gpu_autocapture_egl_prepare_swap_count=0
rdoc_gpu_autocapture_egl_wait_scheduled_count=0
rdoc_gpu_autocapture_egl_vk_lock_count=0
rdoc_gpu_autocapture_egl_vk_unlock_count=0
```

Evidence file:
`build/renderdoc/electron-gpu-autocapture-current/electron-html/evidence.env`.

## Interpretation

This narrows the current Electron failure from a missing summary or late process
death to a frame-trigger coverage gap. The shim is injected and responsive, but
RenderDoc API loading is never attempted because the wrapped Vulkan/EGL/ANGLE
entry points are not reached in this visible-window Electron run.
