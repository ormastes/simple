# Feature Expert — Engine2D ↔ C Vulkan parity (perf matrix + bit-level diff)

## Role

Own process knowledge for comparing Simple's Engine2D 2D lane against an
equivalent C Vulkan program: per-primitive performance, and pixel output
compared byte for byte. This is a measurement harness, not a renderer.

## Pipeline Links

- Plan: `doc/03_plan/ui/engine2d_vulkan_showcase_parity_plan.md`
- NFR: `doc/02_requirements/nfr/engine2d_vulkan_2d_perf.md`
- Research: `doc/01_research/local/2d_rendering_perf_dma_alignment_soa_async.md`
- Bug: `doc/08_tracking/bug/emu_shape_decomposition_emits_one_gpu_dispatch_per_pixel_2026-09-03.md`
- Harness: `test/05_perf/bench/vulkan_2d_c/`

## Gates

| Gate | Question it answers |
|---|---|
| `scripts/check/check-vulkan-2d-c-compare.shs` | throughput ratio vs C |
| `scripts/check/check-vulkan-2d-bit-diff.shs` | do Simple and C produce the SAME PIXELS |
| `scripts/check/check-engine2d-backend-parity.shs` | do Simple's cpu and vulkan backends agree |
| `bin/simple lint --gpu-2d-perf` | the two known per-frame cost shapes (G2DP001/G2DP002) |

## Load-bearing facts

1. **Only 13 of 34 vulkan-backend primitives run on the GPU.** 16 delegate to
   shared `emu_*` CPU code, 5 force a device→host round trip per call. The
   backend NAME describes the lane, not the work. `draw_circle_filled` is GPU
   while `draw_circle` is CPU.
2. **`emu_*` outlines emit one GPU dispatch PER PIXEL** — they decompose into
   1x1 `draw_rect_filled`, which is a memory write on cpu and a compute
   dispatch on vulkan. This is the root cause of the 26-144x cpu-vs-vulkan gap,
   not the shape maths. Span-form (one rect per row) is the fix; it is what
   `emu_draw_circle_filled` already does and why filled shapes are ~25x while
   outlines are ~144x.
3. **Both legs MUST load `test/05_perf/bench/vulkan_2d_c/scenes.txt`.** When each generated
   its own rect set they rendered different pictures (60.1% vs 63.9% coverage)
   and no pixel comparison meant anything. Never re-derive the set per
   language: C's u64 xorshift and Simple's i64 sign-masked variant diverge
   silently.
4. **The parity gate cannot validate an `emu_*` rewrite.** Both backends share
   that code, so both change together and the diff still passes. Capture a
   pre-change framebuffer as a GOLDEN and compare after.
5. **A stride-fold checksum is not a pixel diff.** The bench's `checksum` folds
   every 4096th pixel and self-cancels to 0 over an even frame count. Use the
   bit-diff gate.

## Traps that have cost time

- `SIMPLE_FORCE_INTERPRETER` **does not exist**. A probe that "forced the
  interpreter" ran JIT. Force a real fallback (e.g. trip the field-inference
  gap) and confirm via the `falling back to interpreter` line.
- Measure before naming a cause. Four hypotheses for the big costs (staging
  allocation, per-frame array allocation, `_pixels_to_bytes` upload, native
  `rt_array_copy`) were each plausible and each disproved by measurement; the
  `rt_array_copy` one was a 4x REGRESSION when applied.
- Separate FIRST-CALL from steady-state cost. `draw_rect_blend` measures
  ~330 ms on call 1 and 4.1 ms on call 2.
- The Simple leg intermittently SIGBUSes under MoltenVK. Retry with a bounded
  loop and REPORT the attempt count; never smooth it away silently.
- Machine swing is ~36%, wider than the ±20% the NFR used to claim. Report
  ranges from same-run pairs, not a best run.

## Cross-reference — 2026-09-06 GPU/2D honesty sweep

Vulkan's five-way readback provenance (`backend_vulkan.spl:1468-1519`:
`completion_unknown` / `readback_failed` / `cpu_fallback` / `device_readback` /
`host_cache_after_device_copy`, all five emitted in one readback body) is the repo's reference for an honest provenance
ladder; DirectX's Linux lane was stamping `device_readback` for CPU pixels until
PR #410. Full findings, plus the two unpinned `vulkan_session.spl` seams
(`create_command_buffer()` has no session guard; `_cleanup()`'s zeroing is
vacuous, not a leak) and the self-mocking-spec hazard class, live in
[engine2d_font_offload](../engine2d_font_offload/skill.md) § 2026-09-06.
