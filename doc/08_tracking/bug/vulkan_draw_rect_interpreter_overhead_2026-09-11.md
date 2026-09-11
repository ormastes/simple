# Vulkan `draw_rect_filled` spent 509 us of interpreter time per call (2026-09-11)

Status: **fixed for the dominant terms; target not fully reached, remainder
located and quantified below.**
Host: macOS 25.5 / Apple M4, MoltenVK, interpreter lane
(`SIMPLE_EXECUTION_MODE=interpreter`).
Binary: `bin/release/aarch64-apple-darwin-macho/simple`, 26264696 bytes,
mtime 1788766698 (unchanged across every measurement here).
Prior attribution: `doc/10_metrics/ui/vk2d_bench_frame_time_attribution_macos_2026-09-11.md`.

## Symptom

`test/05_perf/bench/vulkan_2d_c/vk2d_bench.spl` at 900x760, 64 rects/frame ran
at **36.4 ms/frame**, of which ~34 ms was CPU-side interpreter time inside the
per-rect draw path. The GPU enqueued each dispatch in ~24 us and the C
reference did the identical frame in **0.18 ms**. The device was never the
bottleneck.

## Attribution (differential, n=3200 calls, same device, same process)

Each layer timed in isolation, so the numbers subtract rather than nest. `l5` is
the interpreter's floor for a bare `me` call on the same receiver, which is what
makes the others readable. The probe is **tracked and level-gated, default off**
— `VK2D_ATTR=1` on the bench (`VK2D_ATTR_N` sets n), alongside the existing
`VK2D_PROBE=1` loop probe:

```
VK2D_W=900 VK2D_H=760 VK2D_ATTR=1 SIMPLE_EXECUTION_MODE=interpreter ... run vk2d_bench.spl
vk2d-attr n=3200 us_per_call l1_facade=240 l2_backend=214 l3_pack=77 \
  l4_dispatch=97 l5_call_floor=7
```

It deliberately reports no batch-lane per-rect figure: a batch timed inside that
probe read 223 us/rect against the 300-frame `--batch` run's 67, warming did not
change it, and the discrepancy was not isolated — so the probe omits the number
rather than publishing one that contradicts the end-to-end measurement.

| layer | before | after | what it is |
|---|---:|---:|---|
| L3 `_pack_rect_pc` alone | **342 us** | **78 us** | push-constant packing |
| L4 `_dispatch_framebuffer_checked` (pc prepacked) | **96 us** | 96 us | the 4-SFFI enqueue |
| L1-L2 Engine2D facade transit | **22 us** | 23 us | Option unwrap + write-back |
| residue (alpha/mask guards, workgroup math) | ~49 us | ~40 us | |
| L1 total per `Engine2D.draw_rect_filled` | **509 us** | **237 us** | |
| L5 bare `me` call floor | 9 us | 7 us | interpreter call cost |

Top three costs, and what each turned out to be:

1. **Packing, 342 us (67% of the call).** `_pack_rect_pc` built a 64-byte array
   and then made 12 `_pack_*_le(mut buf, ..) -> buf` calls, each of which made 4
   further cast-helper calls (`_i32_to_u32`, `_u32_to_u8`) — ~70 interpreter
   function transits and a pass-and-return of the buffer per rect. Rewritten to
   write every byte inline in one function: **342 -> 78 us**. The push-constant
   LAYOUT is unchanged and still byte-identical to the SPIR-V kernels' block.
2. **The 4-SFFI enqueue, 96 us.** `bind_pipeline`, `bind_descriptors`,
   `push_constants`, `dispatch` — ~24 us per SFFI crossing. Two of the four are
   invariant across rects drawn with the same pipeline.
3. **Facade transit, 22 us.** Small, and left alone: the batch removes it
   structurally by making one transit serve N rects.

There was **no** per-call `text` formatting (the order trace is a cached
boolean) and **no** per-call descriptor creation (the dedup scan hits on the
first entry). Those two suspects were checked and cleared.

## Fix

1. `_pack_rect_pc` / `_write_rect_pc_into`
   (`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl`): inline byte
   writes, no sub-calls, no buffer pass-and-return.
2. `draw_rect_list_filled(rects: [i32], colors: [u32])` — a packed batch entry on
   the Vulkan backend, exposed on `Engine2D`. **The `RenderBackend` trait is
   unchanged**, deliberately: a trait default body was tried first and does NOT
   reach a concrete backend in this compiler (`simple run` on the cpu lane gave
   `semantic: method draw_rect_list_filled not found on type CpuBackend` even
   with the default present, though `read_pixels_damaged` uses the same shape).
   Rather than add a method to every backend for a win only the Vulkan lane can
   realise — every other backend dispatches immediately per primitive, so for
   them the batch IS the loop — the facade routes the non-Vulkan case through
   its own `draw_rect_filled` loop. Frozen layout, mirroring the packed-glyph
   discipline of `backend_vulkan_font.spl`: `rects[4k..4k+4]` = x,y,w,h of rect
   k, `colors[k]` its colour, `rects.len() == colors.len() * 4`. The Vulkan
   override resolves the descriptor and binds pipeline+descriptors ONCE, then
   per rect rewrites only the five words that vary (offsets 0..19 — fb size and
   clip are frame state, hoisted out of the loop) and issues `push_constants` +
   `dispatch`. N rects = 1 interpreter transit, 1 bind, N dispatches, still one
   submission per frame.
3. `--batch` (or `VK2D_BATCH=1`) on the bench runs both legs in one process and
   prints `ms_single=` / `ms_batch=`.

`Engine2D.draw_rect_list_filled` mirrors `draw_rect_filled`'s router arm for arm
(virtio -> baremetal -> cuda -> vulkan), the non-Vulkan arms unpacking into
single calls. **A near-miss worth recording:** an earlier version expressed the
same precedence as a boolean precondition
(`self.virtio_gpu_backend.? == false and ...`), which silently evaluated false on
a plain Vulkan engine and sent every batch down the fallback loop. Both pixel
specs stayed GREEN — the fallback paints identical pixels by construction — and
only the bench caught it, as `ms_batch` jumping from 1999 back to 5382 (i.e. all
the way back to single-call speed). A correctness suite cannot detect a
performance lane being bypassed; the timed comparison is load-bearing evidence
here, not decoration.

Semantics are preserved, not traded: an active stencil mask or ANY non-opaque
colour in the list makes the whole list fall back to the single-rect loop, so a
partial fallback can never reorder painters.

## Result (900x760, 64 rects, 300 frames, interpreter lane)

```
vk2d-compare frames=300 rects=64 ms_single=5286 ms_batch=2012 \
  per_frame_single_us=17620 per_frame_batch_us=6706
```

| lane | ms/frame | vs baseline |
|---|---:|---:|
| baseline (before this change) | 36.4 | 1.0x |
| single call, after the packing fix | **17.62** | 2.07x |
| packed batch | **6.71** | **5.4x** |

`submits_per_frame=1` on both legs.

## Target not reached: 6.71 ms vs the 5 ms goal, and where the rest is

Honest accounting of the remaining 6.71 ms/frame:

- **4.33 ms — interpreter draw time, 67.7 us per rect.** Roughly 30 us of that
  is the ~20 array stores that build the per-rect push-constant words (the
  interpreter charges ~1.5 us per `[u8]` store), and ~35 us is the two
  irreducible SFFI crossings (`push_constants`, `dispatch`) at ~17 us each.
- **2.34 ms — submit + fence wait** for the frame's 65 dispatches. Unchanged by
  this work and not addressed here.

Both remaining terms are per-DISPATCH, so no further host-side batching removes
them: at one dispatch per rect the floor is ~65 us/rect in this interpreter.

## Todo: shader-side batch (the only path below ~1 ms)

Collapsing N rects into ONE dispatch would delete both remaining terms, but it
needs a rect kernel that reads N rects from a storage buffer instead of push
constants. The rect SPIR-V in
`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_spirv.spl:297`
(`spirv_rect_filled`) is a hand-transcribed blob, and per the standing rule
these are not hand-edited. The shader-side batch therefore needs a glslang
build step producing a new pinned blob, and is recorded here as open work
rather than attempted:

- **TODO(perf, gpu):** add a `rect_batch` compute kernel (storage-buffer params:
  count + N x {x,y,w,h,colour}, one dispatch over the union bounding box or a
  per-rect workgroup index) generated by glslang with a pinned SHA, and route
  `_enqueue_rect_batch` onto it. Expected to take the 64-rect frame from 6.7 ms
  to the ~2.4 ms submit/fence floor, and below that once the frame's submission
  is pipelined the way the C leg's 3-deep ring does.

## Evidence

Specs (real device, both refuse to skip — the first expectation is
`backend_name() == "vulkan"`):

- `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_rect_batch_pixel_oracle_spec.spl`
  — **4 examples, 0 failures**. Absolute oracle: 64 rects in an 8x8 grid, the
  centre pixel of cell k must equal `color_for(k)` computed from k alone; the
  batch framebuffer must be byte-identical to 64 single calls across all 65536
  pixels; one submission-generation advance per frame.
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_rect_batch_edges_spec.spl`
  — **4 examples, 0 failures**. Empty list, malformed length pair (paints
  nothing, never a guessed prefix), overlapping rects in painter order, armed
  clip applied to a batched rect.

Sabotage (painter order), on the edges spec:

1. green — `4 examples, 0 failures`
2. batch loop reversed to descend (`k = count - 1; while k >= 0`) —
   `4 examples, 1 failure`, `resolves overlapping rects in painter order, last
   one winning`, `expected 4291572531 to equal 4281558732` (RED found where BLUE
   must win)
3. restored — `4 examples, 0 failures`
