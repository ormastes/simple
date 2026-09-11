# vk2d_bench frame-time attribution (macOS, Apple M4, 2026-09-11)

Post-fix (cherry-picked `2fd65d9b2ac`, `515dd100df4`, `41b31a719d7` onto this
worktree), `test/05_perf/bench/vulkan_2d_c/vk2d_bench.spl` at 900x760, 64
rects, 300 frames, interpreter mode:
`status=blocked reason=unconditional-submit-wait ms=10908 fps~=27 draw_us=10285638 finalize_us=606234`
— **36.4 ms/frame**, not the pre-fix 42 ms/frame quoted in the task (the
batching fix already removed ~5.6 ms/frame of mid-frame-fence cost).

Binary: `bin/release/aarch64-apple-darwin-macho/simple`, 26264696 bytes,
mtime 1788766698 (unchanged across all runs below).

## Method

`build/perf/vk2d_attr_2026-09-11/vk2d_bench_nodraws.spl` — an instrumented
copy (tracked bench untouched) that keeps `clear()` + timing but drops the
`for r in rects: draw_rect_filled(...)` loop, isolating clear+finalize cost
from per-rect draw cost. `VK2D_READBACK` stays 0 (task's command), so
readback is never in the measured region — verified against
`backend_vulkan.spl`/bench source: capture only runs after `t1`.

## Per-frame attribution (300 frames, 5 warmups)

| component | ms/frame | source |
|---|---|---|
| interpreter draw-call overhead (64x `draw_rect_filled`) | **33.9** | `(34285-364)us / frame`, from full run minus nodraws run |
| clear() dispatch (interpreter+enqueue) | 0.36 | nodraws run, `draw_us=109266/300` |
| GPU submit+fence wait (65 enqueued dispatches) | 2.02 | full run, `finalize_us=606234/300` |
| GPU submit+fence wait (1 enqueued dispatch, clear only) | 0.49 | nodraws run, `finalize_us=146353/300` |
| readback | 0 (not exercised; `VK2D_READBACK=0`) | bench source, capture gated on `t1` |
| present | 0 (headless compute-only bench, no swapchain present path) | `backend_vulkan.spl` has no present call in this lane |
| **total measured** | **36.4** | `ms=10908/300` |

Arithmetic: 33.9 (draw calls) + 0.36 (clear) + 2.02 (submit/fence, GPU-side
queuing scales ~24us per extra dispatch: (2021-488)/64) ≈ **36.3 ms/frame**,
matching the reported 36.36 ms/frame within rounding.

**Largest component: interpreter dispatch overhead per `draw_rect_filled`
call, ~530 us/call, at `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:815-852`**
(`me draw_rect_filled`, calling `_dispatch_framebuffer_checked` ->
`_enqueue_framebuffer_compute` at
`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl:379-417` — this
path only *enqueues* into a batched command buffer under
`frame_batching_enabled`, so the 530us/call is CPU-side interpreter+SFFI
dispatch cost per Simple method call, not GPU work). GPU-side cost per
dispatch is ~24us, 22x cheaper.

## C reference comparison

`check-vulkan-2d-c-compare.shs` previously reported `compare_status=skipped`
but every one of its guard conditions (clang, glslangValidator, Vulkan
headers, ICD file) is present on this Mac — reproduced by hand:
`glslangValidator -V rect.comp.glsl -o rect.spv` and
`clang -std=c99 -O2 vk2d_bench.c -I/opt/homebrew/include -L/opt/homebrew/lib -lvulkan -o vk2d_bench`
both succeed, and the binary runs against
`/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json` (MoltenVK, Apple M4) with
no error. The prior skip was environment-state at the time it was recorded,
not a structural block on this host; artifacts in
`build/perf/vk2d_attr_2026-09-11/c/`.

Same workload (900x760, 64 rects, 300 frames), C leg with its 3-deep async
submission ring: `p50_ns=443000 p95_ns=1066000 ms=54.2 fps=5539.9` —
**~0.18 ms/frame average**, ~200x faster than the Simple lane's 36.4 ms/frame.
This confirms the GPU/driver side is not the bottleneck; the gap is
CPU-side dispatch overhead in the interpreter-driven per-rect call path.

## JIT lane

`src/compiler_rust/target/bootstrap/simple run` (no `SIMPLE_EXECUTION_MODE`,
i.e. JIT/native) does **not** hit the known `JIT code arena exhausted` panic
here; it instead falls back before reaching Vulkan at all:
`status=blocked reason=backend-unavailable requested=vulkan got=cpu` — the
JIT lane's `Engine2D.create_with_backend_fast` resolves to the `cpu` backend,
so no JIT-vs-Vulkan comparison is possible from this run.
