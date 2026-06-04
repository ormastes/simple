<!-- codex-research -->
# Domain Research: Harden TUI/GUI Layout Comparison

Date: 2026-06-01

## Visual And Layout Regression Testing

- Visual regression systems generally compare captured UI screenshots with known-good baselines, then produce actual, expected, and diff artifacts. Vitest browser visual regression docs describe screenshot defaults and diff image review: https://v4.vitest.dev/guide/browser/visual-regression-testing
- Current visual testing practice separates exact pixel comparison from perceptual or tolerance-aware comparison. Common stabilizers are fixed viewport, fixed fonts, disabled animations, mocked dynamic data, deterministic waits, ignored regions, and calibrated thresholds.
- Layout comparison should not rely only on pixels. Structural layout data such as element bounds, line breaks, text extents, and clipping state catches root cause earlier and makes failures easier to triage.
- A robust TUI/GUI comparison contract should report: capture source, viewport/cell metrics, font metrics, renderer backend, baseline id, exact match, tolerance match, first mismatch, affected region, and artifact paths.

## Metal

- Apple’s Metal Best Practices Guide emphasizes managing command buffer submission frequency because too many submissions can introduce CPU stalls from CPU/GPU synchronization: https://developer.apple.com/library/archive/documentation/3DDrawing/Conceptual/MTLBestPracticesGuide/CommandBuffers.html
- Apple resource guidance recommends choosing appropriate storage modes and synchronization methods after managed resource writes: https://developer.apple.com/library/archive/documentation/3DDrawing/Conceptual/MTLBestPracticesGuide/ResourceOptions.html
- Design implication: layout/pixel comparison should avoid synchronous readback on every frame. Use batched scenes, explicit readback points, and metrics that separate render time from readback time.

## Vulkan

- The Vulkan Guide notes that synchronization mistakes can cause both correctness bugs and poor performance from unnecessary GPU idling: https://docs.vulkan.org/guide/latest/synchronization.html
- Vulkan tile-based rendering guidance warns that repeated round-trips between GPU and external memory hurt performance: https://docs.vulkan.org/guide/latest/tile_based_rendering_best_practices.html
- Design implication: Vulkan evidence should validate barriers, avoid read-to-read or overly broad barriers in hot paths, batch captures, and report GPU-only timing separately from host readback timing.

## CUDA

- NVIDIA’s CUDA Best Practices Guide identifies coalesced global memory access as high priority and recommends minimizing host/device transfers: https://docs.nvidia.com/cuda/cuda-c-best-practices-guide/index.html
- CUDA optimization evidence should include transfer volume, kernel count, launch overhead, occupancy/register pressure where available, and whether comparisons run on device or after host readback.
- Design implication: CUDA should be a backend evidence lane only on hosts with CUDA hardware/runtime available; otherwise the test should fail closed or record unavailable, not claim performance.

## SIMD CPU

- LLVM documents loop and SLP vectorizers, default vectorization, runtime pointer checks, reductions, if-conversion, and diagnostics: https://llvm.org/docs/Vectorizers.html
- Intel vectorization guidance highlights data layout, unit-stride aligned memory access, and avoiding unsupported operations in SIMD loops: https://www.intel.com/content/www/us/en/developer/articles/technical/vectorization-llvm-gcc-cpus-gpus.html
- Design implication: CPU SIMD comparison should use contiguous pixel buffers, branch-light per-channel diff loops, explicit scalar fallback, and a verification report that proves vectorization or records why scalar fallback was selected.

## Binary Size And Startup Performance

- Native size optimization should prefer dead-code elimination, section garbage collection, LTO, PGO-guided layout, and optional backend packaging so unused GPU backends do not bloat baseline TUI/GUI tools.
- Performance evidence must distinguish cold startup, warm startup, steady-state frame/render latency, capture latency, readback latency, and max RSS.

## Domain Conclusion

The safest architecture is a two-layer comparison system: structural layout diffs for deterministic TUI/GUI geometry and pixel/perceptual diffs for rendered output. GPU/SIMD acceleration should be measured through backend-qualified lanes with fail-closed availability checks, not broad claims. Size/perf work should keep optional backends out of the default hot path and require evidence per target.
