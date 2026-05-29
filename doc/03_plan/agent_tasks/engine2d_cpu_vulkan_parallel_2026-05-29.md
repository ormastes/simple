# Engine2D CPU/Vulkan Parallel Rendering Note - 2026-05-29

## Scope

- Inspected `src/lib/gc_async_mut/gpu/engine2d/backend_cpu.spl`, `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl`, `src/lib/gc_async_mut/gpu/engine2d/engine.spl`, and focused `test/integration/rendering/engine2d_*_spec.spl` files.
- Left protected shared planning docs untouched.
- No `backend_cpu.spl` source change was made because the focused CPU behavior checked here did not show a CPU-backed divergence.

## Change

- Added `test/integration/rendering/engine2d_cpu_vulkan_parity_spec.spl`.
- The new spec keeps a compact core primitive scene and verifies:
  - CPU rendering is deterministic.
  - CPU rendering is bit-exact against the software reference for clear, filled/outline rects, line, circle, filled circle, triangle, gradient, and clipping.

## Vulkan Availability

- Host Vulkan is present:
  - Command: `timeout 20s vulkaninfo --summary`
  - Result: `STATUS=0`; saw Vulkan instance `1.3.275`, NVIDIA TITAN RTX, NVIDIA RTX A6000, and llvmpipe CPU device. `DISPLAY` and `XDG_RUNTIME_DIR` warnings were present but summary completed.
- Engine2D Vulkan path could not be used for pixel parity on this host in the current checkout:
  - Temporary probe command: `timeout 60s bin/simple test/integration/rendering/engine2d_tmp_probe.spl`
  - Result: `PIPE_STATUS=1`; CPU backend initialized, then the Vulkan request failed with `error: semantic: function expects argument for parameter 'mode', but none was provided`.
  - The temporary probe file was removed.

## Commands And Results

- `timeout 45s bin/simple check src/lib/gc_async_mut/gpu/engine2d/backend_cpu.spl`
  - PASS: `All checks passed (1 file(s))`.
- `timeout 60s bin/simple check src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl`
  - PASS with warnings: unresolved import when checking the file standalone without source root, and a gc boundary warning.
- `timeout 120s bin/simple test test/integration/rendering/engine2d_cpu_vulkan_parity_spec.spl --mode=interpreter`
  - PASS: 2 passed, 0 failed, duration 1063ms.
- `timeout 120s bin/simple test test/integration/rendering/engine2d_drawing_spec.spl --mode=interpreter`
  - PASS: 2 passed, 0 failed, duration 945ms.
- `timeout 90s bin/simple test test/integration/rendering/engine2d_clip_spec.spl --mode=interpreter`
  - PASS: 3 passed, 0 failed, duration 687ms.
- `timeout 90s bin/simple test test/integration/rendering/engine2d_mask_spec.spl --mode=interpreter`
  - PASS: 3 passed, 0 failed, duration 692ms.
- `timeout 90s bin/simple test test/integration/rendering/engine2d_text_spec.spl --mode=interpreter`
  - PASS: 3 passed, 0 failed, duration 1051ms.
- `timeout 180s bin/simple test test/integration/rendering/engine2d_primitives_spec.spl --mode=interpreter`
  - PASS: 24 passed, 0 failed, duration 90497ms.
  - Runner flagged this as `[PERF BUG]`.
- `timeout 60s bin/simple test test/integration/rendering/engine2d_backend_spec.spl --mode=interpreter`
  - FAIL/TIMEOUT: `PIPE_STATUS=124`; test started but produced no pass/fail summary before timeout.

## Remaining Blockers

- Direct CPU-vs-Vulkan pixel parity is blocked by the current Engine2D Vulkan execution failure: `function expects argument for parameter 'mode', but none was provided`.
- Backend discovery/lifecycle coverage is not usable as a quick focused check right now: `engine2d_backend_spec.spl` times out at 60s, likely in backend probing.
- `engine2d_primitives_spec.spl` passes but takes about 90s and is flagged by the runner as a performance bug.
