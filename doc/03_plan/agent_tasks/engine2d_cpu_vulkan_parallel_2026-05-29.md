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
- Superseded blocker: this note originally recorded Vulkan pixel parity as
  blocked by runtime GLSL compilation and placeholder SPIR-V blobs. The later
  Linux live Vulkan fix replaced that blocker with validated SPIR-V shader
  modules, interpreter SFFI support for shader modules/buffer upload/readback,
  push constants, and a compute-to-host memory barrier.
- Current authoritative status: direct CPU-vs-Vulkan pixel parity is closed for
  this Linux restart pass. See
  `doc/03_plan/gui_renderer_restart_plan_2026-05-29.md` for the live Vulkan
  verification evidence.

## Commands And Results

- `timeout 45s bin/simple check src/lib/gc_async_mut/gpu/engine2d/backend_cpu.spl`
  - PASS: `All checks passed (1 file(s))`.
- `timeout 60s bin/simple check src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl`
  - PASS with warnings: unresolved import when checking the file standalone without source root, and a gc boundary warning.
- `SIMPLE_LIB=src timeout 60s bin/simple test test/integration/rendering/engine2d_cpu_vulkan_parity_spec.spl --mode=interpreter --clean --format json`
  - PASS: 3 passed, 0 failed.
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
- `SIMPLE_LIB=src timeout 60s bin/simple test test/integration/rendering/engine2d_backend_spec.spl --mode=interpreter --clean --format json`
  - PASS: 8 passed, 0 failed after narrowing this smoke to the always-available
    software and CPU backend lifecycle path.

## Remaining Follow-Ups

- Direct CPU-vs-Vulkan pixel parity is no longer blocked in the current
  checkout; the earlier shader-path note above is retained only as historical
  context.
- `engine2d_primitives_spec.spl` passes but takes about 90s and is flagged by the runner as a performance bug.
