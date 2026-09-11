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

---

# Shader-side follow-up (2026-09-11): N rects, ONE compute dispatch

The host-side batch above removed the per-rect interpreter TRANSIT but still
recorded N `vkCmdPushConstants` + N `vkCmdDispatch` — two SFFI calls per rect.
This follow-up moves the rect list into a GPU storage buffer and paints the whole
batch with a single dispatch.

## What landed

- `src/lib/gc_async_mut/gpu/engine2d/shaders/rect_batch.comp` — GLSL compute
  kernel. Binding 0 framebuffer, binding 1 rect list (5 u32 per rect:
  x, y, w, h, colour), 48 bytes of push constants (bbox x/y/w/h, n, fb w/h,
  clip x/y/w/h, clip_enabled). One invocation per bounding-box pixel; each walks
  the rect list in ASCENDING index order and keeps the LAST covering rect, which
  is exactly what N sequential single-rect dispatches produce. The frame-bounds
  and clip guards are transcribed from `_glsl_rect_filled` so the batch is
  pixel-exact against N singles.
- `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_rect_batch_spirv.spl` —
  GENERATED word array + pinned sha256. The `.spv` is a build intermediate and is
  deliberately NOT checked in.
- `scripts/tool/spirv-to-spl-words.shs` (od-based transcriber, emits the sha256
  pin line) and `scripts/tool/gen-rect-batch-spirv.shs` (compile + rewrite the
  module). Reproducible: `glslangValidator -V --target-env vulkan1.1`.
- `scripts/check/check-rect-batch-spirv-pinned.shs` — recompiles the `.comp` and
  compares bytes AND the pinned sha against the committed module. Fail-closed;
  a host with no `glslangValidator` is `ERROR — nothing was checked`, never a
  pass. `--selftest` (4 fixtures, fatal, runs before every scan) uses a
  self-contained fixture GLSL rather than the real `.comp`, because coupling it
  to the tree made it abort exactly when the guard was most needed.
- Wiring: `vulkan_session.spl` compiles the SPIR-V and creates
  `pipe_rect_batch` as an OPTIONAL pipeline — a failure records
  `rect_batch_error` and leaves the host loop running rather than failing
  session init. `_enqueue_rect_batch_gpu` (backend_vulkan_helpers.spl) uploads
  the packed list, sets push constants once, and records one dispatch.
  `draw_rect_list_filled` prefers it at `n >= RECT_BATCH_MIN_RECTS` (2) and
  falls back to the F4 host loop on any decline.

### Mid-frame buffer reuse (the bug this design invites)

`copy_to_buffer` writes at RECORD time; the dispatch reads at SUBMIT time. One
reused rect-list buffer would therefore let a SECOND batch in the same frame
silently repaint the FIRST batch's dispatch. The lane uses a per-frame SLOT POOL
(mirroring `font_params_pool`/`image_descriptor_pool`): a slot is claimed at most
once per frame and `rect_batch_slot` resets only in
`_clear_pending_compute_state`, i.e. after the fence. Pinned by the
"keeps two batches in one frame on two separate slots" example.

## Measurement — 900x760, 64 rects, 300 frames

Same tree, same binary (`bin/release/aarch64-apple-darwin-macho/simple`,
`26264696 1788766698` before and after each run), interpreter lane, toggled ONLY
by `RECT_BATCH_MIN_RECTS` (2 = GPU lane; 1000000 = forced F4 host lane).

| lane | dispatches/frame | ms/frame | draw (host) | finalize (submit+GPU) |
|---|---|---|---|---|
| F4 host batch | 64 | 6.663 | 4.28 ms | 2.34 ms |
| GPU rect batch | **1** | 6.686 | 3.71 ms | 2.94 ms |

(single-rect lane, for scale: 17.37 ms/frame.)

**Honest finding: wall clock is flat.** The deliverable — one dispatch, rect list
resident on the GPU — is achieved and proven, but it did not buy time at this
size. The 0.57 ms of per-dispatch SFFI cost that disappeared was replaced by
0.60 ms of extra GPU work. Both halves are named below rather than averaged away.

## Three named gaps (none closed here)

0. **The rect-list upload is its OWN blocking queue submit — the lane is NOT one
   submit per frame.** `vulkan_sffi_copy_to_buffer` -> `rt_vulkan_copy_to_buffer`
   -> `Buffer::upload_at` (`src/compiler_rust/runtime/src/vulkan/buffer.rs:338`)
   unconditionally builds a staging buffer and calls `copy_from_staging`, which
   ends in `device.submit_transfer_command(cmd)` (`:537`) — a real
   `queue_submit` plus fence wait (`device.rs:902,940`). So a batched frame is
   one COMPUTE submit plus one TRANSFER submit per batch, and part of the
   draw-side 3.71 ms is that blocking GPU round-trip rather than interpreter
   work. This was NOT caught by the pixel oracle's "one device submission"
   example, because `vulkan_submission_generation()` counts only the compute
   submits `_flush_pending_compute` makes. It is very likely the single biggest
   reason the wall clock came out flat: N cheap record-only dispatches were
   traded for one dispatch plus one synchronous device round-trip. Fixing it
   needs an SFFI that RECORDS `vkCmdCopyBuffer` into the already-open compute
   command buffer instead of submitting its own; no such entry point exists
   today (`vulkan_sffi_copy_to_buffer` is the only upload).
1. **Host packing is the dominant O(N) interpreter term in the 3.71 ms
   draw-side residual — by construction, not separately timed.** (`draw_us`
   also contains the clear, the bounding-box loop, the upload above, and four
   record-time SFFI calls; only their sum was measured.)
   The rect list must be built as `[u8]`: the interpreter's array marshaller
   `strict_owned_bytes` (`src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:633`,
   and its twin in `dynamic_sffi.rs:769`) truncates EVERY element to one byte and
   errors above 255, so a `[u32]`/`[i32]` upload is rejected outright — there is
   no typed buffer upload in the Vulkan SFFI. 64 rects x 20 stores = 1280
   interpreter array stores per frame. Closing this needs a width-aware upload
   facade (then bindings could take `[i32]` rects and `[u32]` colours directly
   with zero host repacking), which is a seed change.
2. **The per-pixel rect walk is O(bbox_pixels x N) — a real regression on the GPU
   axis, 2.34 ms -> 2.94 ms.** At 900x760 with 64 rects that is ~43.8M loop
   iterations, most of them misses. Candidate fix, not built here: a per-workgroup
   tile cull (skip a 16x16 tile's whole rect walk when the tile intersects no
   rect), or a coarse tile-to-rect bucket list uploaded alongside the rects.

## Evidence

- `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_rect_batch_one_dispatch_spec.spl`
  — NEW, **7 examples, 0 failures** on device. Device identity and a
  no-fallback-reason precondition (both RED without a real ICD), then
  `rect_dispatches_for_batch(64) == 1`, the `n == 2` boundary, `n == 1` staying
  on the single-rect lane, `n == 0` recording nothing, and the two-batch slot
  guard above (3 dispatches, all four probe pixels correct).
- `backend_vulkan_rect_batch_pixel_oracle_spec.spl` — **4 examples, 0 failures**
  re-run against the GPU lane (verified live via
  `SIMPLE_VK_ORDER_TRACE=1`, which emits `rect-batch-gpu pipe=23 n=64 slot=0
  bbox=0,0,256,256`). The 64-rect batch is still byte-identical to 64 singles.
- `backend_vulkan_rect_batch_edges_spec.spl` — **4 examples, 0 failures**.
- Bench: `vk2d_bench.spl --batch` now prints `dispatches_per_frame=1` and
  `rect_batch_fallback=none`.

### Sabotage 1 — the pinned-blob guard (tampered word)

1. `PASS — 5848 byte(s) compared ... (sha256 6292ffa5...)`
2. one word changed `0x11u8 -> 0x12u8` in the committed module —
   `FAIL — 5848 byte(s) compared: committed words differ from freshly compiled
   GLSL (... differ: char 62, line 21 ...)`, exit 1
3. restored — `PASS — 5848 byte(s) compared ...`

### Sabotage 2 — the shader (reversed per-pixel rect walk)

This one deliberately shows the two guards are COMPLEMENTARY, not redundant:

1. green: pin `PASS`, edges spec `4 examples, 0 failures`
2. `.comp` loop reversed to `for (k = pc.n - 1; k >= 0; --k)`, blob NOT
   regenerated — pin `FAIL — 5868 byte(s) compared: byte count differs:
   committed 5848, freshly compiled 5868` (catches the stale blob)
3. blob regenerated from the reversed GLSL — pin `PASS — 5868 byte(s) compared
   ... (sha256 0ad41001...)`. **The pin cannot catch a semantic change**, which
   is the honest limit of a byte pin.
4. edges spec on that build — `4 examples, 1 failure`, `resolves overlapping
   rects in painter order, last one winning`, `expected 4291572531 to equal
   4281558732`. The spec is what catches it.
5. `.comp` restored + regenerated — pin `PASS — 5848 byte(s) compared ...
   (sha256 6292ffa5...)`, edges spec `4 examples, 0 failures`.
