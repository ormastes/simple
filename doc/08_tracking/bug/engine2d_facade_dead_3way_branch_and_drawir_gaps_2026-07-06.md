# Maintenance: Engine2D facade has dead 3-way branch (~35 methods) + Draw-IR coverage gaps

- **Date:** 2026-07-06
- **Severity:** LOW-MEDIUM (dead code burden, coverage mismatch)
- **Area:** src/lib/gc_async_mut/gpu/engine2d/engine.spl, scene.spl, engine2d_executor.spl, compute_dispatch.spl

## Summary

The Engine2D facade repeats an identical 3-way `if val Some(vg) ... elif val Some(bm) ... else backend...` branch across ~35 drawing methods, even though every constructor sets `baremetal_backend`/`virtio_gpu_backend` to the identical object as `backend:` itself. All three paths are always the same instance and the branch is dead code. Additionally, Draw-IR (`SceneCommand`) coverage does not match `RenderBackend` trait coverage: a scene_blur_rect constructor produces kind `"blur_rect"` but the executor has no branch for it (silently drops); triangle/mask kinds exist in the trait but not in the IR; a second backend-selection path (`compute_dispatch.spl`) disagrees with the render path on what backends are available.

## Evidence

- **Dead 3-way branch:** ~35 methods across `engine.spl` repeat the pattern (samples: `clear` :534-541, `draw_ellipse` :651-657, `draw_arc`, `draw_bezier`, etc.). Every constructor (`create_with_baremetal_backend_dims` :305, `create_with_virtio_gpu_backend` :309) sets `backend:`, `baremetal_backend:`, and `virtio_gpu_backend:` to the identical underlying object. Confirmed by audit: all three arms call the exact same line (e.g. emu_draw_X(self.backend, ...)) for the 18 extended ops; for the rest, branch is provably dead by constructor inspection.

- **blur_rect silently dropped:** `scene.spl:111-112` defines `scene_blur_rect()` constructor producing kind `"blur_rect"`. Executor if-chain `engine2d_executor.spl:37-77` has branches for `fill_rect, stroke_rect, text, line, circle, circle_filled, rounded_rect, gradient_rect, image, clip_push, clip_pop` but **no branch for `"blur_rect"`** — scene with blur command is never executed.

- **Triangle/mask trait methods unused in IR:** `RenderBackend` (backend.spl:21-44) defines `draw_triangle_filled`, `set_mask`, `clear_mask` but `RenderScene`/`SceneCommand` have no corresponding kinds. These trait methods are reachable only from direct `Engine2D` API callers, never from Draw-IR executor paths.

- **Compute dispatch disagrees with render probe:** `compute_dispatch.spl` uses `BackendProber`/`_strict_probe_backend` (backend_probe.spl:107-148) which has **no branch at all for cuda/opencl**, permanent `Unavailable` for rocm, never probes vulkan/metal/webgpu. Meanwhile `Engine2D.probe_backend()` (engine.spl:323-412) performs real per-class probes for all of them. Same backend name can return different availability answers depending on which path is called.

- **Miswired CPU-SIMD detection:** `backend_probe.spl:122` `probe_cpu_simd_x86()` calls `_strict_probe_backend("cpu_simd")` (generic always-true branch line 109) instead of the real NEON/AVX-detecting branch (lines 128-136) it should hit. Test at engine_platform_spec.spl:70-82 asserts cuda/rocm/opencl.probe.has_compute == true, which is structurally impossible given `_strict_probe_backend` code today (contradiction not executed in read-only audit; flagged for empirical follow-up).

## Failure scenario

1. Maintainer edits one of the 35 methods to add a new feature or fix a bug in the middle branch
2. Assumes all three paths need the same edit; updates one but misses the others (though they are identical)
3. Future edge case or constructor variant accidentally makes `vg` or `bm` diverge from `backend:`, making the branch no longer dead
4. Silent misrouting to wrong backend instance; symptoms appear far downstream

For Draw-IR:
1. Scene-builder constructs a scene with blur_rect commands (valid API call)
2. Passes to Engine2D executor, which silently drops blur without warning or error
3. Visual output is missing blur; no indication the command was dropped

## Fix direction

1. **Collapse dead branch:** replace all 35 `if val Some(vg) ... elif val Some(bm) ... else self.backend` with just `self.backend` (or the appropriate struct field). Verify no constructor ever diverges them; add an assertion at constructor entry if needed.

2. **Add executor branches:** if blur_rect is a live feature, add executor branch for kind `"blur_rect"` at engine2d_executor.spl line ~70 that dispatches to `engine.draw_blur_rect()` or similar. If blur is unfinished, remove `scene_blur_rect()` constructor entirely.

3. **Unify backend-selection paths:** make `compute_dispatch.spl` use the same backend probe logic as `Engine2D.probe_backend()`, or consolidate them into one shared function. Ensure both paths return the same availability answer for the same backend name.

4. **Fix CPU-SIMD detection:** `backend_probe.spl:122` should call `_strict_probe_backend("cpu_simd_x86")` on x86_64 (or `"cpu_simd_arm"` on ARM), not the generic `"cpu_simd"` branch. Verify the test at engine_platform_spec.spl:70-82 is actually runnable and matches the code logic.

5. **Add unused-kind lint:** if triangle/mask are not supported by the executor, either add executor branches or mark them as `@deprecated` in the trait with a comment explaining they're only for direct `Engine2D` API calls.

## Verification targets

- The dead 3-way branch is replaced by direct field access; 35 methods compile without semantic change
- `scene_blur_rect()` either executes as expected in a scene, or constructor is deleted with zero dangling references
- `Engine2D.detect_best_backend()` and `compute_dispatch.select_best()` return identical availability answers for cuda, rocm, opencl, metal, vulkan, webgpu
- CPU-SIMD probe on ARM64 and x86_64 detects real NEON/AVX (if available) rather than always returning true
- Test at engine_platform_spec.spl:70-82 runs and either passes or is updated to reflect what the code actually does
