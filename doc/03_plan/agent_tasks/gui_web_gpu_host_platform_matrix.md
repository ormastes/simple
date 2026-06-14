# GUI/Web Host-GPU Platform Evidence Matrix

Date: 2026-06-14

## Scope

Track the remaining host-specific proof needed for production-level GUI/web 2D
Engine2D queue/readback evidence after the Linux Vulkan/CUDA work. This is a
coordination plan for parallel agents; do not use it as proof by itself.

## Canonical Gate

Run from repo root:

```sh
BUILD_DIR=build/production_gui_web_host_gpu_queue_readback_<agent> \
SIMPLE_BIN=src/compiler_rust/target/debug/simple \
SIMPLE_LIB=src \
sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

The report is:

```text
doc/09_report/production_gui_web_host_gpu_queue_readback_YYYY-MM-DD.md
```

## Parallel Work Items

### Linux Vulkan/CUDA Agent

Owns:
- `scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs`
- `src/lib/gc_async_mut/ui/web_render_pixel_backend.spl`
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_*readback*`
- BrowserBackend runtime queue specs.

Acceptance:
- `browser_first_backend_handle` remains `0` for BrowserBackend queue-local
  evidence until a real opaque backend runtime handle is plumbed through the
  frame receipt. Synthetic handle `7` is valid only in isolated runtime queue
  roundtrip tests, not in BrowserBackend production evidence.
- `browser_first_gpu_readback_source` is not `cpu_mirror`.
- `readback_vulkan_verdict=pass`.
- `readback_cuda_verdict=pass` on CUDA-capable Linux.
- Overall production wrapper exits `0`.

### macOS Metal Agent

Owns only Metal host evidence and reports.

Commands:

```sh
sh scripts/check/check-metal-generated-2d-readback.shs
BUILD_DIR=build/production_gui_web_host_gpu_queue_readback_macos \
sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

Host requirements:
- macOS/Darwin host.
- `xcrun metal` and `xcrun metallib` or equivalent tools.
- `system_profiler SPDisplaysDataType`.
- Working `bin/simple` or `SIMPLE_BIN`.

Acceptance:
- Metal direct readback report is `pass`.
- Production wrapper records Metal as `pass` on macOS, not Linux unavailable.

### ROCm/HIP Agent

Owns only ROCm/HIP host evidence and reports.

Commands:

```sh
HIP_ARCH=${HIP_ARCH:-gfx1100} sh scripts/check/check-rocm-generated-2d-readback.shs
BUILD_DIR=build/production_gui_web_host_gpu_queue_readback_rocm \
sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

Host requirements:
- AMD ROCm-capable host/device.
- `hipcc`, `rocminfo`, ROCm loader libraries.
- Verified HSACO for the selected `HIP_ARCH`.

Acceptance:
- ROCm generated 2D readback has a real pass path instead of
  `missing-rocm-submit-readback-harness`.
- Production wrapper records ROCm/HIP as `pass` on a ROCm host.

### Windows/DirectX Agent

Owns only DirectX evidence planning unless a Windows host is available.

Current state:
- DirectX is not part of the production queue/readback wrapper.
- Linux DXVK setup exists but is setup/plumbing, not production proof.

Acceptance:
- Add a DirectX wrapper only after a real D3D/DXVK readback command exists.
- Do not mark DirectX production-ready from setup scripts alone.

## Do Not Touch

- Unrelated SSH/crypto/RISC-V work.
- Vendored runtime sources.
- MCP/LSP/package files.
- Other agents' dirty files unless they are explicitly part of this matrix.
