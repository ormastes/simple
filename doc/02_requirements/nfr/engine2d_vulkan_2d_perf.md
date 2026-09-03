# NFR: Engine2D Vulkan 2D throughput vs C reference

- **Date:** 2026-09-03
- **Status:** measured baseline; targets below
- **Research:** `doc/01_research/local/2d_rendering_perf_dma_alignment_soa_async.md`,
  `doc/01_research/domain/2d_renderer_gpu_offload_patterns.md`
- **Harness:** `bench/vulkan_2d_c/` (C reference adapted from the Magicalbat
  single-file headless Vulkan compute example; Simple counterpart driving
  Engine2D), gated by `scripts/check/check-vulkan-2d-c-compare.shs` +
  `test/03_system/check/engine2d_vulkan_2d_perf_contract_spec.spl`

## Workload (identical both sides)

Per frame: full-screen clear + 64 rect fills (24–184 px, deterministic
xorshift64 set, ~60% coverage) + frame submit + fence + full-frame readback.
800×600 u32 framebuffer, 300 frames, Apple M4 via MoltenVK 1.4.350.

## Measured baseline

| Lane | fps | ms/frame | note |
|---|---|---|---|
| C reference, readback | **1089** | 0.92 | 1 submit + 1 fence/frame; HOST_COHERENT map = free readback |
| C reference, no readback | 1094 | 0.91 | readback costs ~0.005 ms/frame in C |
| C reference, 360 rects | 407 | 2.46 | per-dispatch ≈ 1.9 µs |
| Simple Engine2D, readback | **43** | 23.0 | phases below |
| Simple Engine2D, no readback | 59 | 16.9 | |

Simple per-frame phase attribution (300-frame run):

| Phase | ms/frame | share |
|---|---|---|
| draw calls (clear + 64 rect FFI) | 1.3 | 6% |
| submit_batch + present | 13.2 | 57% |
| readback (marshalling) | 8.4 | 37% |

## Perf gap

**Simple = 4.0% of C (readback) / 5.4% (no readback) — a 18–25× gap.**
The gap is entirely host-side strategy, not the GPU or the shaders:

1. submit+present blocks on fences/transfers per frame (~13 ms),
2. readback pays interpreted marshalling (~8 ms; C pays ~0),
3. per-rect FFI encoding (~1.3 ms; C pays ~0.12 ms for the same 64
   dispatches).

## Targets

| ID | Target | Verification |
|---|---|---|
| NFR-2DP-001 | `compare_ratio_x1000 ≥ 100` (Simple ≥ 10% of C) at 800×600/64 rects | `check-vulkan-2d-c-compare.shs` evidence.env (current: 39 — FAILING, tracked) |
| NFR-2DP-002 | ≥ 50% of C after the frame-batching + delayed-readback rework (research fix list 1,2,5) | same harness, budget raised |
| NFR-2DP-003 | comparator never emits a fake pass: missing toolchain leg ⇒ `compare_status=skipped` with reason | contract spec, 3 synthetic cases |

## Environment caveats

Numbers shift ±20% under load; the Simple lane additionally shows
intermittent SIGBUS under memory pressure
(`doc/08_tracking/bug/vulkan_engine2d_sequential_frames_flaky_moltenvk_2026-09-02.md`).
The gate compares same-machine, same-device, same-workload runs, so relative
ratio is the metric, never absolute fps.
