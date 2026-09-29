# Web showcase CPU<->GPU boundary audit (macOS M4, 2026-09-12)

> **CORRECTION (2026-09-12, same day): ranked defects 2 and 4 below name the
> WRONG file.** Presenter-owned counters (`[web-route-stage]`, now drained per
> frame by the gate) read `readbacks_upload=0 readbacks_gpu_paint=0
> host_paint_pixels=0` on this exact lane: the presenter is not on the audited
> path at all, because the default lane reaches
> `simple_web_layout_engine2d_fast.spl:1260` and only consults the presenter's
> A/B route under `SIMPLE_WEB_GPU_PAINT=1`, which this gate does not set. The
> two readbacks are (1) the parent-material "glass" seed at
> `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl:2583` — a FULL-surface read
> cropped on the host, re-uploaded into an offscreen delta and composited back,
> the real device->host->device pass-through — and (2) the final frame read.
> Cutting the count to <=1 needs device-side glass on the Vulkan backend.
> Evidence, counters and handoff:
> `doc/08_tracking/bug/web_presenter_double_readback_and_host_paint_passthrough_2026-09-12.md`.

Gate `scripts/check/check-web-vulkan-gpu-boundary-audit.shs`, aggregator
`src/app/ui/chrome_showcase/gpu_boundary_audit.spl`, spec
`test/01_unit/app/ui/gpu_boundary_audit_spec.spl`, bootstrap row
`web-vulkan-gpu-boundary-audit-selftest`. Binary `build/cargo-r2/release/simple`,
`stat -f '%z %m'` bracketed before/after every run: r1-r5 on **A** = `39368072
1789171430`, r7/r6b/r4b on **B** = `39178424 1789197971` — a peer replaced it
mid-run, **the gate's bracket caught it**, voiding r6; ms do not compare across. Interpreter mode, serial runs, logs in
`build/perf/gpu_audit_4k_2026-09-12/`; page `web_catalog/overview.html` except
r6. Lane flags: `SIMPLE_2D_BACKEND=<b>
SIMPLE_VK_READBACK=native SIMPLE_VK_IMAGE_UPLOAD=u32 SIMPLE_VK_RECT_UPLOAD=u32`
(full set, and why `SIMPLE_VK_FONT_SELFCHECK=1` is NOT armed, in the gate header).
Counters come from `sffi_*` buckets, NOT the pooled census, where
`submits=`/`fences=` read 0 against 17 real submits.

## Runs

| run | size | backend | cold ms | steady ms | verdict |
|---|---|---|---|---|---|
| r1 | 900x760 | vulkan | 126,293 | 102,287 | FAIL |
| r2 | 3840x2160 | vulkan | 181,033 | (1 frame) | FAIL |
| r7 | 3840x2160 | vulkan | no frame | — | ERROR (binary B) |
| r3 | 1920x1080 | vulkan | 141,312 | 253,105 | FAIL |
| r4/r4b | 1920x1080 | cpu_simd | 197,315 (r4 SIGTERM @233 s) | 170,140 | ERROR (not Vulkan) |
| r5 | 3840x2160 | cpu_simd | >1,200,000 rc=124 | not reached | ERROR (timeout) |
| r6 / r6b | 900x760 css-layout | vulkan | no frame | — | ERROR (swap / B) |

**GPU vs CPU at 4K: Vulkan 181 s cold, cpu_simd >1200 s — a >6.6x floor, not a
ratio** (the CPU run never produced a frame); both are binary A. 1080p GPU/CPU
straddles the binary swap and is NOT comparable. r4's SIGTERM was a
one-off, cause unattributed (r5 ran 1210 s past the same mark). **Binary B blocks
every further Vulkan run:** `unknown extern function: rt_vulkan_copy_to_buffer_u32`
— the typed u32 upload lane is gone, voiding r7 (the 4K steady frame) and r6/r6b
(the substitute, `wm_web_standards_showcase_gui` emitting no lane census).

Audit keys, per frame, **identical at 900x760 and 3840x2160**:
`submits_per_frame=17 dispatches_per_frame=107 readbacks_per_frame=2
uploads_per_frame=94 upload_mode=u32 host_pixel_iterations=16
host_pixel_buckets=font_atlas_pack_u32_to_u8:16 cpu_fallback_count=0
full_surface_composites=0 atlas_full_repacks=5 fence_waits=17`. Only
`readback_bytes` differs: **5,472,000 -> 66,355,200**. `upload_bytes` and an exact
`host_pixel_iterations` are `unavailable` (no counters exist); a `pack_full x
1,048,576` lower bound is emitted instead of a zero. r4b/r5 ERROR by design — a non-Vulkan lane makes every counter a structural
zero, and passing that is the "unmeasured zero fakes a PASS" failure this gate
refuses; frame times stay valid. ms are an envelope, the COUNTS are the bar.

## Verdicts

`FAIL — <n> frame(s) audited, violated: host_pixel_iterations=16 (>0):
font_atlas_pack_u32_to_u8:16; readbacks_per_frame=2 (>1); submits_per_frame=17
(>1)` — identical at both sizes. Gate selftest: `PASS — selftest only, 6 examples,
0 failures` (clean PASS, host loop FAIL, 2 readbacks FAIL, wrong lane ERROR,
disarmed timing ERROR, empty log ERROR). **`simple test` runs no spec on this
host**, so the spec has never executed — pre-existing `access_cli_spec.spl` fails
byte-identically; the selftest proves the classifier instead, 6/6.

## Ranked boundary defects

**The boundary is already node-scaled.** Every count is byte-identical at 900x760
and 3840x2160 across 12.1x the pixels; only `readback_bytes` grows. Frame time
grows just 1.8x (102.3 -> 181.0 s) and the document pipeline is flat, so the
pixel-scaled cost is host rasterization: the non-nested vk-timing buckets are
**~61 s of the 102.3 s frame (60%) but only ~55 s of the 181.0 s 4K frame (30%)**
— ~41 s -> ~126 s of host paint no GPU op touches. Classes: (a) interpreted
per-pixel loop, (b) per-op upload, (c) host readback, (d) sync wait, (e)
pixel-scaled work.

1. **(a)+(e) Full 1024x1024 atlas repack on every font-identity flip** —
   `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font.spl:1212-1274`
   (`can_increment` :1236-1244). 16 packs/frame, `pack_full=5 pack_incremental=11`,
   `identity_changed=5`, size-independent. `font_composite` = 59,478 ms (58% of
   the 900x760 frame) / 52,227 ms (29% at 4K), largest Vulkan term at both;
   >=5,242,880 host pixel writes. ONE host mirror, so each flip repacks all
   1,048,576 pixels. **Fix:** per-owner mirror keyed on owner identity.
2. **(c)+(e) Two full-surface readbacks/frame — the only pixel-scaled boundary
   term.** 4K `readback_pixels=16,588,800` (2 x the 8,294,400-px surface) =
   66,355,200 B, vs 1,368,000 px / 5,472,000 B at 900x760. Presenter
   `read_pixels_with_source()` sites: `simple_web_html_engine2d_presenter.spl:436`
   (damage blit) and `:598` (full surface). Honest gap: `readback` shows `n=1` as
   `VK_T_READBACK` is only in `read_pixels()` (`backend_vulkan.spl:2146`), which
   both bypass. **Fix:** one readback/frame via the timed wrapper.
3. **(b)+(e) The whole 4 MB atlas re-uploads on every pack, dirty rects ignored**
   — `backend_vulkan_font.spl:1276`, `vulkan_sffi_copy_to_buffer(d_font_atlas,
   font_atlas_host_bytes, 0)`: the entire 1024x1024x4 mirror at offset 0
   unconditionally — and it is the file's ONLY write to `d_font_atlas`, so no
   dirty-rect path exists, although `batch.dirty_rects` is computed and used by
   the self-check above. 16/frame = **~64 MB/frame**. **Fix:** send dirty rects.
4. **(e) The presenter uses the GPU as a pass-through** —
   `simple_web_html_engine2d_presenter.spl:593-598`: the page is rasterized on the
   HOST into `pixels`, uploaded via `engine.draw_image(0,0,w,h,pixels)` and read
   straight back — the ~126 s of 4K host paint. **Fix:** paint on device.
5. **(d) One submit + one fence wait per font run** — `sffi_submit_and_wait n=17`,
   `sffi_wait_fence n=17` against `font_composite n=18`, one-to-one; 107 dispatches
   over 17 submits — 48 ms, but 17 round trips against an invariant of 1. **Fix:**
   one command buffer, one fence per frame.
6. **(b) 78 image uploads/frame, no identity key** — `backend_vulkan.spl:1373-1392`
   (`image_source_alloc n=78`, pooled via `_acquire_image_source`). Pooling makes
   this not an allocation defect: the same pixels re-upload every frame with no
   producer-generation key. **Fix:** key on `(identity, generation)`.

## Appendix — device backdrop blur lands (2026-09-12, F33)

Re-measured with `scripts/check/check-web-vulkan-gpu-boundary-audit.shs` on
`overview.html`, 900x760, 2 frames, interpreter, `SIMPLE_2D_BACKEND=vulkan
SIMPLE_VK_READBACK=native SIMPLE_VK_IMAGE_UPLOAD=u32 SIMPLE_VK_RECT_UPLOAD=u32`,
binary `build/cargo-r2/release/simple` (`39528776 1789199850`).

| key | before | after |
|---|---|---|
| `readbacks_per_frame` | 2 | **1** |
| `readback_bytes` | 5,472,000 | **2,736,000** |
| `uploads_per_frame` | 25 | 24 |
| `submits_per_frame` | 17 | 17 |
| `host_pixel_iterations` | 16 | 16 |

Page pixels are byte-identical (full-page FNV-1a digest
`-3650045829680336039` before and after, both frames).

**Correction to this document's defect #2/#4 attribution.** The second
full-surface readback was NOT the parent-material glass seed in
`draw_ir_adv.spl` — that branch never runs on this lane (every `[vk-order]`
line in the frame carries the same `fb=3`, so no offscreen delta surface is
ever created). It was `VulkanBackend.draw_blur_rect`, which had no device
implementation and delegated to the host `emu_draw_blur_rect`: a whole-surface
`read_pixels()`, an interpreted box blur, and a re-upload — silently, with
`cpu_fallback_count` reading 0 throughout. Detail and the trace evidence:
`doc/08_tracking/bug/vulkan_glass_seed_host_roundtrip_2026-09-12.md`.

Still open here: the `image-composite w=888 h=384 mode=1` that precedes the
blur is a 340,992-pixel host-sourced upload each frame — the remaining half of
defect #4, a different producer, untouched by this change.

### Final numbers, rebased onto `origin/main` @ `7001fa826e6`

| key | pristine base | with device blur + glass |
|---|---|---|
| `readbacks_per_frame` | 2 | **1** |
| `readback_bytes` | 5,472,000 | **2,736,000** |
| `submits_per_frame` | 2 | **1** |
| `uploads_per_frame` | 24 | **23** |
| `frame_digest` | `a15c50cd` | `a15c50cd` |

The kernels are RECORDED into the frame's command buffer rather than flushed:
every `rt_vulkan_dispatch` already emits a full memory barrier, so no
submission is needed to make the earlier dispatches' writes visible to a kernel
that samples them. Flushing instead would have removed the readback while
leaving the submit count where it was.

Only `host_pixel_iterations=15 (font_atlas_pack_u32_to_u8)` still violates.

## Appended 2026-09-12 — typed font-atlas upload (`SIMPLE_VK_FONT_UPLOAD=u32`), gate now PASSes

Same binary throughout (`build/cargo-r2/release/simple`, `39528776 1789199850`,
identity bracketed before and after every run), overview.html 900x760, 2 frames.

| key | bytes lane | u32 lane |
|---|---|---|
| verdict | FAIL `host_pixel_iterations=23` | **PASS** |
| `host_pixel_iterations` | 23 (`font_atlas_pack_u32_to_u8:15`, `image_pack_u32_to_u8:8`) | **0** (`none`) |
| `host_pixel_iterations_lower_bound` | 4,194,304 | **0** |
| `atlas_full_repacks` | 4 | 0 |
| `upload_ms` | 146 | **45** |
| `submits_per_frame` | 1 | 1 |
| `readbacks_per_frame` | 1 | 1 |
| `dispatches_per_frame` | 107 | 107 |
| `uploads_per_frame` | 23 | 23 |
| `fence_waits` | 1 | 1 |
| `frame_digest` | `a15c50cd` | `a15c50cd` |

```
PASS — 2 frame(s) audited, host_pixel_iterations=0, readbacks_per_frame<=1, submits_per_frame<=1
```

css-layout.html 900x760, 2 frames, same binary: `host_pixel_iterations` 47
(`font:20`, `image:27`) -> **0**, `upload_ms` 184 -> 58, `frame_digest`
`811c9dc5` on both lanes. That page still FAILs on `submits_per_frame=3 (>1)`,
a pre-existing violation of a different lane.

Sabotage control: byte-swapping each word inside the typed upload left every
count identical and moved `frame_digest` to `acadc75d`; reverting restored
`a15c50cd`.

Residual: the 15 font-atlas uploads per frame are now ~60 MB of runtime memcpy
instead of 15 million interpreted host stores — net strongly positive
(`upload_ms` 146 -> 45), but the upload COUNT (one per text run rather than one
per owner per frame) is a separate lane's defect. Detail:
`doc/08_tracking/bug/vulkan_font_atlas_host_pack_last_host_loop_2026-09-12.md`.
