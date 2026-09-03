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

## Measured, 2026-09-03 (after the readback rework)

| Lane | fps | ms/frame | note |
|---|---|---|---|
| C reference, readback | 1371–1595 | 0.63–0.73 | same machine/device as the row below |
| Simple Engine2D, readback | **81–128** | 7.87–12.3 | `compare_ratio_x1000 = 59–79` |

Three consecutive gate runs on a loaded shared machine gave ratios 79, 59
and fps 128/127/81 against C 1260/1595/1371. **Report the range, not the
best run**: the swing (~36%) is wider than the ±20% this doc previously
claimed, and any single number here is noise-dominated. The pre-fix ratio
was measured the same way (25) so the improvement is real, but "79" alone
would be cherry-picked.

Simple per-frame phase attribution (300-frame run):

| Phase | ms/frame | share |
|---|---|---|
| draw calls (clear + 64 rect FFI) | 0.64 | 8% |
| submit_batch | 2.28 | 29% |
| present (device→host refresh) | 2.38 | 30% |
| readback (`read_pixels_with_source`) | 2.57 | 33% |

Two host-side defects were found by attribution and fixed:

1. **Array returned through a tuple deep-copies it.**
   `vulkan_sffi_readback_u32_checksum(...) -> ([u32], i64)` cost **~12.1 ms
   per frame** at 800×600 in the tuple return alone — more than the device
   download and the native fill combined (~3.6 ms). Assigning the *same*
   array costs 22 µs, so the cost is the tuple boundary, not the array.
   Replaced with `vulkan_sffi_readback_u32_into(dest, ...) -> i64`, which
   also lets `host_buf` be reused instead of reallocating 480,000 elements
   per frame (~0.35 ms).
   Result: **fps 32 → 81–128, present 21.84 → 2.24 ms/frame, ratio 25 → 59–79**
   (range over three runs on a loaded machine; see the variance note above).

2. **Per-element copy loop** (`copy[i] = self.host_buf[i]`) in
   `read_pixels_with_source`, ~2.57 ms/frame. Still open — it is the largest
   remaining single phase. `rt_array_copy` exists in the runtime but has no
   Simple-level surface.

Both shapes are now caught mechanically by the `gpu_2d_perf` lint
(G2DP001/G2DP002, `bin/simple lint --gpu-2d-perf`), which independently
re-finds defect 2 at `backend_vulkan.spl:1504`.

### Workload fidelity caveat (found 2026-09-03)

The two legs do **not** render an identical rect set. C seeds an unsigned
`u64` xorshift with `0x9e3779b97f4a7c15`; the Simple bench uses the same
constant as `i64` (where it is negative), masks with `0x7FFFFFFFFFFFFFFF`
after each shift and sign-flips. The sequences therefore differ, despite the
docstring claiming "same distribution". Measured coverage: C 288,504
non-clear pixels (60.1%), Simple 306,818 (63.9%) — Simple does ~6% *more*
fill work, so the ratio understates Simple rather than flattering it. This
also explains why the two legs report different checksums; readback
correctness was confirmed separately (`px[0]=0xFF141414`, 480000/480000
non-zero on both). Worth fixing before the ratio is read to two digits.

## Measured baseline (superseded, kept for history)

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
| NFR-2DP-001 | `compare_ratio_x1000 ≥ 100` (Simple ≥ 10% of C) at 800×600/64 rects | `check-vulkan-2d-c-compare.shs` evidence.env (current: **59–79** over three runs — still FAILING, up from 25; tracked) |
| NFR-2DP-002 | ≥ 50% of C after the frame-batching + delayed-readback rework (research fix list 1,2,5) | same harness, budget raised |
| NFR-2DP-003 | comparator never emits a fake pass: missing toolchain leg ⇒ `compare_status=skipped` with reason | contract spec, 3 synthetic cases |

## Environment caveats

Numbers shift ±20% under load; the Simple lane additionally shows
intermittent SIGBUS under memory pressure
(`doc/08_tracking/bug/vulkan_engine2d_sequential_frames_flaky_moltenvk_2026-09-02.md`).
The gate compares same-machine, same-device, same-workload runs, so relative
ratio is the metric, never absolute fps.
