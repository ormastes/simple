# GPU Headless Host Testing

Verified 2026-08-02 on the Linux dev host (RTX A6000 + TITAN RTX, no display
attached). The Vulkan engine2d lane is fully headless-capable: it never creates
a `VkSurfaceKHR`/swapchain — rendering targets a device storage buffer
(`d_framebuffer`) and results come back via buffer readback
(`source=device_readback`). No X11/Wayland is required for that lane.

## Host requirements

| Requirement | How to check | Notes |
|---|---|---|
| Vulkan loader + ICDs | `ls /usr/share/vulkan/icd.d` | Need `nvidia_icd.json` (real GPU) and/or `lvp_icd.json` (lavapipe software) |
| Device node access | `ls -la /dev/nvidia*` | NVIDIA nodes are world-rw; no group needed. Mesa drivers instead need the `render` group for `/dev/dri/renderD*` (`id` must list `render`) |
| Headless enumeration | `env -u DISPLAY vulkaninfo --summary` | Works without any display; lists all GPUs + llvmpipe |
| Software fallback | `ls /usr/lib/x86_64-linux-gnu/libvulkan_lvp.so` | lavapipe; swiftshader not installed on this host |
| X fallback for display lanes | `which xvfb-run Xvfb` | Only needed for SDL/GLFW/Electron paths |

## Verified recipes

### 1. Real-GPU headless (Vulkan readback lane) — VERIFIED PASS

```bash
env -u DISPLAY -u WAYLAND_DISPLAY SIMPLE_TIMEOUT_SECONDS=3600 \
  bin/simple test test/02_integration/rendering/vulkan_buffer_readback_bytes_spec.spl --timeout 1700
# Results: 1 total, 1 passed, 0 failed   (exit 0)
```

### 2. Software Vulkan (lavapipe) — VERIFIED PASS

For hosts without a GPU, or to pin CI to a deterministic device:

```bash
env -u DISPLAY -u WAYLAND_DISPLAY \
  VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/lvp_icd.json \
  SIMPLE_TIMEOUT_SECONDS=3600 \
  bin/simple test test/02_integration/rendering/vulkan_buffer_readback_bytes_spec.spl --timeout 1700
# Results: 1 total, 1 passed, 0 failed   (exit 0)
```

### 3. xvfb-run fallback (display-needing lanes only)

```bash
xvfb-run -a env SIMPLE_TIMEOUT_SECONDS=3600 \
  bin/simple test <spec> --timeout 1700
```

## Lane classification

Headless-safe (offscreen buffer + readback; no window system linked):

- `test/02_integration/rendering/vulkan_buffer_readback_bytes_spec.spl` (proven)
- `test/02_integration/rendering/engine2d_cpu_vulkan_parity_spec.spl`
- `test/02_integration/rendering/web_engine2d_gpu_offload_parity_spec.spl`
  (observed `source=device_readback handle=1` on this host)
- `test/03_system/gui/engine2d_gpu_offload_contract_spec.spl`
- `test/03_system/gui/web_showcase_full_gpu_offload_spec.spl`
- Any spec driving `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl` /
  `vulkan_session.spl` — these files contain no surface/swapchain/GLFW code.

Display-needing (use xvfb-run, or a real session):

- SDL present path (`src/runtime/runtime_sdl2.c`):
  `test/02_integration/rendering/sdl_present_failure_contract_spec.spl`
- GLFW path (`src/runtime/runtime_glfw.c`) and
  `src/lib/nogc_sync_mut/io/window_sffi.spl` consumers:
  `test/02_integration/ui/event_backend_matrix_spec.spl`
- Electron/Chromium web-render helper
  (`src/lib/gc_async_mut/gpu/browser_engine/web_render_backend.spl`,
  `SIMPLE_WEB_RENDER_ELECTRON` / `SIMPLE_WEB_RENDER_HELPER` knobs) — Electron
  needs an X server; wrap with `xvfb-run -a`.

## Relevant env knobs

- `SIMPLE_2D_BACKEND` — engine2d backend selection
  (`src/lib/gc_async_mut/gpu/engine2d/engine.spl`)
- `VULKAN_GLSL_ENABLED` — GLSL pipeline toggle (`backend_vulkan_glsl.spl`)
- `VK_ICD_FILENAMES` — pin the Vulkan ICD (lavapipe for software CI)
- `SIMPLE_WEB_RENDER_TMP`, `SIMPLE_WEB_RENDER_ELECTRON`,
  `SIMPLE_WEB_RENDER_HELPER` — web render offload lane

## CI notes

- Always run with `env -u DISPLAY -u WAYLAND_DISPLAY` for the Vulkan readback
  lanes so an accidental X dependency fails loudly instead of passing only on
  desktop hosts.
- Pin `VK_ICD_FILENAMES` to lavapipe on GPU-less runners; results are
  deterministic across machines.
- Exit 255 with zero output means the 60 s monitor timeout, not a crash —
  re-run with `SIMPLE_TIMEOUT_SECONDS=3600 ... --timeout 1700` and read the
  log's own `Results:` line from a captured file, not the terminal tail.
- For Mesa-driver runners, add the CI user to the `render` group or the
  `/dev/dri/renderD*` open fails and lavapipe silently becomes the only device.
