# Vulkan 2D backend: mid-frame fence waits and clip-disabled GPU text (2026-09-11)

Group **F2** of `doc/03_plan/ui/gpu_offload/web_vulkan_cpu_gpu_boundary_fix_plan_2026-09-11.md`
(census rows R4, R5, R6, R8, R9 of
`doc/01_research/ui/gpu_offload/cpu_gpu_boundary_census_2026-09-11.md`).

Status: **FIXED**, with device evidence on a real Apple M4. Pure Simple only; no
`src/runtime` or Rust-seed edit, and no new `rt_*`/SFFI was needed.

## Binary and host identity (bracketing every run below)

```
bin/release/aarch64-apple-darwin-macho/simple   26264696 bytes, mtime 1788766698 (2026-09-07)
run as: SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0 <binary> run <file>
device reported by the backend: Apple M4
  (driver Apple M4|vendor=0000106b|device=1a040209|driver=000028a1|api=0040014e)
```

`bin/simple` in this worktree is a dangling symlink (`stat` -> "No such file"),
so the Sep-7 macho path above is named explicitly in every command. One tree,
one binary, one toggle per measurement.

## R5 — `draw_text_bg` fenced the whole batch before every band

`backend_vulkan_font.spl:690-703` (pre-fix) called `_flush_pending_compute()` ->
`vulkan_sffi_submit_and_wait_fence` (`backend_vulkan_helpers.spl:418`) before
each background band, to order the band's rect dispatch before the glyph
dispatch. The in-source TODO asserted a `vulkan_sffi_pipeline_barrier` was
needed and did not exist.

**The fence was redundant and the premise was wrong.** `rt_vulkan_dispatch`
(`src/compiler_rust/runtime/src/vulkan_graphics_runtime_compute.rs:469-496`,
read-only) records `cmd_dispatch` and then, unconditionally, a `VkMemoryBarrier`
via `cmd_pipeline_barrier` with masks from `dispatch_memory_barrier()` (:456-465):
`src = COMPUTE_SHADER / SHADER_WRITE`, `dst = COMPUTE_SHADER|TRANSFER /
SHADER_READ|SHADER_WRITE|TRANSFER_READ`. A Rust unit test at :504-523
(`dispatch_barrier_orders_compute_writes_before_compute_and_transfer_reads`)
pins those masks. Every dispatch in the batch is therefore already ordered
against the next one, so the band is visible to the glyph dispatch with no
submit. The flush is deleted and replaced with that citation.

**Device A/B** (300 rects + 20 unclipped `draw_text_bg` bands, one frame):

| | submits | fences | text path |
|---|---|---|---|
| before (`HEAD~1` source) | **21** | **21** | font-atlas-batch |
| after | **1** | **1** | font-atlas-batch |

Read from `observed_device_submit_count` / `observed_device_fence_count` after
`finalize_compute_frame_no_readback()`. Reverting the fix alone restores 21/21;
restoring it returns 1/1 — that is the sabotage triple for R5, run on the device.

## R4 — a scissor disabled the GPU glyph lane entirely

`vulkan_bitmap_text_atlas_block_reason` returned
`clip-unsupported-by-font-composite` for every clipped run
(`backend_vulkan_font.spl:569-570`), so `draw_text` fell to `text_blit_buffer` +
`draw_image_blend` — a CPU raster and an image upload per run, i.e. essentially
all ~5000 glyphs of a clipped 4K page.

**Deviation from the task's prescription, stated explicitly.** The task said to
add the clip to the glyph compute push constants and clamp in "the SPIR-V emitted
by `backend_vulkan_font_spirv.spl` (it is generated in Simple)". That premise is
false: that file is a **transcribed glslangValidator blob** with a pinned
`FONT_ATLAS_COMPOSITE_VULKAN_SPIRV_SHA256` (its own header says "Regenerate with
glslangValidator -V; validate with spirv-val"), its GLSL source lives at
`test/09_baselines/engine2d_vulkan/font_atlas_packed.comp`, and the packed params
layout is frozen for Metal-twin parity (PR #376) which this agent does not own.
The shortest correct diff is therefore to **bake the axis-aligned scissor into
the quads on the host** before packing — new pure function
`vulkan_bitmap_text_clip_quads` — advancing `atlas_x`/`atlas_y` by the amount cut
off the left/top and shrinking `width`/`height`. Because the composite reads
`atlas[atlas_x + u, atlas_y + v]` for `u < width`, this selects exactly the
surviving sub-rect and is pixel-identical to letting the CPU path clip the blit.
Zero shader change, zero layout change, fully testable device-free. The
`clip_enabled` parameter is renamed `clip_unbakeable` with an updated docstring;
mask and non-opaque-colour block reasons are unchanged.

**Device A/B** (300 rects, `set_clip(0,0,400,300)`, then `draw_text`):

| | `last_text_path` | `last_text_fallback_reason` |
|---|---|---|
| before | `cpu-raster-blit` | `clip-unsupported-by-font-composite` |
| after | `font-atlas-batch` | `` (empty) |

## R6 — fixed 256-entry pending dispatch table

`pending_compute_pipelines/descriptors/sources` were `[0i64; 256]`
(`backend_vulkan.spl:412-414`, `:696-698`, `backend_vulkan_helpers.spl:333-335`),
and overflow at `helpers:481-488` / `:510-513` forced a mid-frame
`_flush_pending_compute` = submit + fence wait. All three are now grown by
`push`; both overflow blocks are deleted.

**Is there a hard upper bound in the SFFI? No — cited.**
`rt_vulkan_create_descriptor_set`
(`src/compiler_rust/runtime/src/vulkan_graphics_runtime_compute.rs:19-70`) creates
a **fresh `VkDescriptorPool` per descriptor set** (`max_sets = 16` at :44), so
there is no global `maxSets` ceiling and no SFFI limit on dispatches recorded
into one command buffer. No hard cap is therefore imposed. The 256 constant
survives only where it was always a host-memory bound: the retained image-source
staging pool, extracted as `VK_IMAGE_SOURCE_POOL_CAPACITY`
(`backend_vulkan_helpers.spl`), which previously read the pending table's length
and would otherwise have become dynamic.

**Census correction.** The census claims ">=8 fence waits for 2000 rects" for
this row. That is wrong for plain rects: `_enqueue_framebuffer_compute`
(`helpers:466-470`) de-duplicates the descriptor **per pipeline**, so 2000
same-pipeline rects consume ONE table slot. Confirmed on device — 300 rects
gave `pending_compute_count = 0` after one flush and only ever 1 submit, both
before and after this change. The cap was only reachable via
`_enqueue_image_composite`, which consumed one slot per call. R6 is therefore a
real but narrower fix than the census states; R5 was the dominant mid-frame
fence source, and the device A/B above shows it.

## R8 — host coverage atlas rasterised per `draw_text`

`atlas_pixels: vulkan_bitmap_font_atlas_pixels(...)` was built unconditionally at
`backend_vulkan_font.spl:641` and then discarded by the generation cache at
`:820-828` unless `font_atlas_generation`/`font_atlas_owner_identity` changed —
both derived from `scale`. New method `_bitmap_font_atlas_pixels` memoises on
`(scale, glyph_height_px)`, the same identity the device cache keys on, and
counts real rasters in `font_atlas_cpu_build_count`. Device probe: two text calls
in one frame -> `atlas_builds=1`.

## R9 — descriptor set per composited image

`vulkan_sffi_create_descriptor_set(pipe)` ran per enqueued image composite
(`helpers:525`). Now pooled in `image_descriptor_pool` by position within the
batch, mirroring the font lane's `font_params_pool`/`font_descriptor_pool`
(`backend_vulkan_font.spl:846-861`). Position `k` is claimed at most once per
batch and every earlier batch that used it was submitted and fence-waited by
`_flush_pending_compute`, so rebinding cannot touch a set live in an unsubmitted
command. `_release_pending_compute_descriptors` skips pooled sets;
`_quarantine_pending_compute_descriptors` drops the pool wholesale;
`shutdown` destroys it. This removes one whole `vkCreateDescriptorPool` per
composited image, not merely one allocation (see the R6 runtime citation).

A pooled descriptor is reachable from BOTH `pending_compute_descriptors[i]` and
`image_descriptor_pool`, so `_quarantine_pending_compute_descriptors` would have
quarantined one handle twice and reaped a second destroy of an already-destroyed
set. The pending loop now passes `0` for a pooled descriptor, exactly as it
already did for a pooled source on the next argument. This is a failure-path-only
defect; no spec catches it, and it is recorded here rather than claimed covered.

## Specs (two per fix, beside the nearest existing spec)

`test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_batch_and_clip_boundary_spec.spl`
— **7 examples, 0 failures**, entirely device-free.

| row | reproducing | generalizing |
|---|---|---|
| R6 | `starts a frame with no preallocated dispatch ceiling` | `records zero mid-frame flushes before any primitive is enqueued` |
| R8 | `rasterises the host coverage atlas once for a repeated draw size` | `rebuilds the host atlas when the glyph identity actually changes` |
| R4 | `no longer blocks the glyph lane merely because a scissor is set` + `clips a glyph run to the scissor with a known pixel at a fixed point` | `keeps, drops and trims adjacent glyphs consistently across the scissor` |
| R5 | device A/B above (21 submits -> 1); `records zero mid-frame flushes...` covers the counter | device A/B, sabotage triple |
| R9 | `records zero mid-frame flushes...` asserts the pool starts empty | device-unverified, see below |

Absolute oracle in the clip scenario: the composited colour at local `(0,0)` of a
quad clipped 2px from the left must equal the unclipped quad's colour at `(2,0)`,
evaluated through `font_atlas_subrect_pixels` — the same subrect the SPIR-V
kernel implements — and `(1,0)` vs `(3,0)` as a second point.

## Which assertions ran on a device, and which did not

**On the Apple M4 device:** every number in the R5 and R4 A/B tables
(`observed_device_submit_count`, `observed_device_fence_count`,
`pending_compute_count`, `last_text_path`, `last_text_fallback_reason`), plus
`font_atlas_cpu_build_count = 1` for R8, via a scratch probe that calls
`VulkanBackend.init(800,600)`, 300 `draw_rect_filled`, `set_clip`, `draw_text`,
`draw_text_bg` and `finalize_compute_frame_no_readback()`. The Vulkan SFFI **is**
admitted under the Sep-7 macho binary in interpreter mode — the plan's blanket
"Vulkan SFFI is REFUSED on this Mac" is not true for this lane and the
`environment-blocked` framing was not needed.

**What the committed spec CANNOT catch, stated rather than implied.** It pins the
SEMANTICS of `vulkan_bitmap_text_atlas_block_reason`, not the call-site wiring: a
sabotage that re-passes `self.clip_enabled` at `backend_vulkan_font.spl:617`/`:686`
would leave all 7 examples green. Only the device probe in the R4 table
discriminates that. Likewise the R9 double-quarantine repair above is on a
failure path no spec reaches.

Note on `midframe_flush_count`: it is CUMULATIVE since create/shutdown and is
never reset per frame. The device probe's `midframe_flush = 1` is the single
FINAL flush at `finalize_compute_frame_no_readback`, not a mid-frame one — the
point being that there were no others.

**NOT on a device:** the whole of the committed spec file (deliberately — it must
run on a GPU-less host), and **R9's pooling behaviour**. The probe reported
`img_pool = 0` because with R4 fixed all text takes the atlas lane and no image
composite is enqueued at all, so the pool was never exercised on hardware. R9's
reuse path is reviewed and device-free-asserted only at its empty initial state.
Unblock condition: a device probe that forces `_enqueue_image_composite` (a
`draw_image` with a non-opaque or masked source, or text with a mask set) across
two frames and asserts `image_descriptor_pool.len()` stops growing.

## vk2d_bench

`test/05_perf/bench/vulkan_2d_c/vk2d_bench.spl` (not owned by this agent) reports
`status=blocked reason=unconditional-submit-wait`. That string is a **hardcoded
literal in its own report line at :173**, not a computed gate — it is a static
claim about the backend, so it does not change when the backend does. Measured on
the M4 after the fix: `ms=10454 fps~=28 p50_ns=34683000 p95_ns=35567000
fence_completions=300 cpu_completion_wait_count=300` at 800x600 / 64 rects / 300
samples. **Before/after on the same tree and binary, as requested:**

| | fence_completions | cpu_completion_wait_count | p50_ns | ms | fps |
|---|---|---|---|---|---|
| before (`HEAD~1` source) | 300 | 300 | 34922000 | 10514 | 28 |
| after | 300 | 300 | 34737000 | 10686 | 28 |

Unchanged, and that IS the finding: **the bench does not reach any of the fixed
paths.** It draws 64 same-pipeline rects with no `draw_text_bg`, no clipped text
and no image composite, so it already ran at one fence per frame before the fix
(see the R6 census correction) and R5/R6/R9 have nothing to act on there. The
172 ms delta is run-to-run noise on a shared machine, not a regression. The
coordinator's `ms=1982` figure is from a different geometry (900x760) and is not
comparable to either row. Action for the bench's owner (not this agent's file):
`status=blocked reason=unconditional-submit-wait` and
`unconditional_submit_wait=true` at :173 are hardcoded literals and should be
computed from `observed_device_submit_count` / `observed_device_fence_count`, or
they will keep reporting a blocked backend after the block is gone.

## Runtime needs

**None.** `vulkan_sffi_pipeline_barrier` was NOT required — the runtime already
emits the barrier (R5 above). No
`.spipe/simple_2d_web_renderer_gpu_optimization/state.md` record was created
because no `rt_*`/SFFI addition was contemplated after that finding.

## Files

- `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl`
- `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font.spl`
- `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl`
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_batch_and_clip_boundary_spec.spl`

`backend_vulkan_font_spirv.spl`, `backend_vulkan_font_types.spl` and
`backend_accel_vulkan.spl` are unchanged — see the R4 deviation above for why the
SPIR-V blob was not touched.

## Pre-existing red, untouched

`backend_vulkan_font_spec.spl` reports **22 examples, 5 failures** both before and
after this change (verified by restoring pristine sources in the same tree with
the same binary). The five are `font-pipeline-semantics-mismatch` /
`invalid-font-params` / `variable 'target' not found` failures unrelated to F2.
