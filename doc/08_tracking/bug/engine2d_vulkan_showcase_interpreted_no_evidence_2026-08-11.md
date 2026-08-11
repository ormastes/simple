# Engine2D Vulkan showcase under interpreter: no evidence within 280s at 320x240 (backend creation itself works)

- **Date:** 2026-08-11
- **Severity:** medium (vulkan showcase evidence unobtainable in the interpreter lane; native lane untested this session)
- **Area:** src/lib/gc_async_mut/gpu/engine2d/backend_vulkan*.spl interpreted render path

## Observed
- Minimal probe (`scratchpad/vulkan_probe.spl`, terminal):
  `Engine2D.create_requested_backend(64,64,"vulkan")` → `created backend=vulkan`
  — Vulkan init + device selection work on this host (MoltenVK via Homebrew),
  even with a sanitized `env -i` environment.
- Full showcase (`graphics_2d_showcase_gui.spl`, `SIMPLE_GUI_BACKEND=vulkan`,
  320x240, rust gui driver, terminal): **no `graphics_2d_*` evidence lines after
  280s** (rc=124). The same showcase on metal completes the render in ~2-3 min
  interpreted; on cpu_simd it completes (blank, see
  interp_engine2d_cpu_lane_mutation_lost_blank_frame_2026-08-11.md).
- Via the `.app` launcher (`scripts/gui/macos-gui-run.shs`), vulkan falls back
  to `cpu` with **empty** `graphics_2d_vulkan_fallback_reason` — the fallback
  path does not record why vulkan was rejected, and the resulting cpu frame is
  the same blank interpreter frame (semantic_differences=0 → gate fail).

## Update 2026-08-12 (post cpu-lane write-back fix)
Terminal run with `SIMPLE_SHOWCASE_TRACE=1` (320x240, gui driver, 420s):
`entry → engine_created → font_candidate_resolved → font_loaded → draw_begin →
cleared` then **no further stage for the remaining ~6.5 min** (rc=124). So the
Vulkan device/session init and even the framebuffer clear complete; the stall is
inside the post-clear draw stage (per-op SFFI command marshalling under the
interpreter is the prime suspect). The `.app` lane still falls back to `cpu`
(which since the write-back fix renders full content, semantic_differences=4),
and `graphics_2d_vulkan_fallback_reason` is still empty. The vulkan-fallback
run also reports `graphics_2d_font_backend_attempt_succeeded=false` despite
`cpu:success` in the font attempt list — an evidence inconsistency to fix with
the reason propagation.

## Notes
- The whole showcase module is dropped to the interpreter by the JIT
  (`_sorted_timer_stats` closure ABI + unresolved
  `rt_directx_execute_readback_checked` extern in the seed), so every Vulkan
  command is marshalled per-op through the interpreter; vulkan likely hits the
  same wall as interpreted_engine2d_full_res_render_slow_2026-07-02 but worse
  (per-op SFFI marshalling of vertex/uniform data).
- `vulkan_cpu_fallback_reason` staying empty on the fallback path is a separate
  evidence bug: `create_with_backend` → cpu fallback does not propagate
  `VulkanBackend.last_error` into the engine the caller receives.

## Fix direction
1. Record the vulkan init/init-stage failure reason into the fallback engine so
   `graphics_2d_vulkan_fallback_reason` is never empty.
2. Give the vulkan backend a no-mirror/fast path equivalent to
   `MetalBackend.use_gpu_only()` so interpreted vulkan is measurable at all.
3. Re-run this showcase once the full CLI (dynload native) is deployable again
   (blocked by stage4_surface_fingerprint_mismatch_log_modes_2026-08-11.md).
