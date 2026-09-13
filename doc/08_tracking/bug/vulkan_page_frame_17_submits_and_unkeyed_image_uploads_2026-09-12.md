# Vulkan web-page frame: 17 submits/fence waits and 78 unkeyed image uploads (2026-09-12)

Status: **#6 FIXED and measured** (78 image uploads/frame -> 9). **#5 NOT fixed,
but for the first time ATTRIBUTED** — 30 of 45 flushes are the font lane's, which
this change does not own. Details and the exact residual below.

Subject: `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl`,
`backend_vulkan_helpers.spl`. Measured by
`scripts/check/check-web-vulkan-gpu-boundary-audit.shs` on
`examples/06_io/ui/web_catalog/overview.html` at 900x760, 2 frames, interpreter
mode, macOS M4. Defect list source:
`doc/10_metrics/ui/web_4k_showcase_gpu_boundary_audit_macos_2026-09-12.md`
(ranked defects #5 and #6).

## What was wrong

**#5 `submits_per_frame=17 fence_waits=17` against an invariant of 1.** Every
submit on the batched path comes from exactly one `_flush_pending_compute`
(`backend_vulkan_helpers.spl`), the sole caller of
`vulkan_sffi_submit_and_wait_fence` there. So the count was never the open
question — **which of the 20 call sites produced each one** was, and nothing in
the tree could answer it. The audit's reading ("one-to-one with `font_composite
n=18`") is a count coincidence, not an attribution: 17 is equally `16 atlas packs
+ 1 finalize` or `18 composites - 1`. Acting on it would have meant editing a
file this change does not own, on a guess.

**#6 `uploads_per_frame=94`, of which 78 are images, with no identity key.**
`_draw_image_composite_native_impl` uploaded the caller's `[u32]` into a pooled
device buffer on **every** call, every frame. Pooling (`_acquire_image_source`)
had already removed the per-image *allocation*; what remained was the per-image
*copy*, and nothing in the path could tell "the same pixels as last frame" from
"new pixels", because a raw `[u32]` carries no identity and F17 found no O(1)
array identity to lean on. Measured shape of that population on the real page:
**76 of the 78 composites are 1x1** and 2 are 888x384.

## The fix

**Attribution, not guesswork (#5).** `_flush_pending_compute_at(site)` arms
`pending_flush_site`; `_flush_pending_compute` moves it into `last_flush_site`
and disarms, so an *untagged* flush reports `untagged` rather than inheriting the
previous caller's name. The `[vk-order] flush` trace prints `site= rc= pending_n=
font_n=`, with `pending_n`/`font_n` captured **before** the impl runs — it ends in
`_clear_pending_compute_state`, so reading them afterwards printed 0 every time
and the attribution this record rests on would have been vacuous. Every flush
site in the two owned files names its enclosing method; the two font-lane sites
(`backend_vulkan_font.spl:1112,1182`) are deliberately left untagged and are
identified by `site=untagged` together with `font_n>0`.

**A key, consumed before anything can reject the draw (#6).** `hint_image_key(key)`
arms a one-shot producer identity, mirroring `hint_damage`/`consume_damage_hint`.
`_draw_image_composite_native_impl` consumes it on its **first line**, before every
validation return: a key names THIS call's pixels, and leaving it armed on a
clipped-out or rejected composite would hand that identity to the next, unrelated
image, which would then skip a genuine upload on a later frame and draw the wrong
pixels. `image_source_pool_key` runs parallel to `image_source_pool`;
`_acquire_keyed_image_source` returns a slot only when the key matches **and the
capacity matches exactly** — a larger slot holds a previous, larger image and only
its prefix would be these pixels. On a hit the upload is skipped entirely. A
*pending* slot is reusable here, unlike `_acquire_image_source`: two dispatches
reading one buffer is no hazard, whereas handing out a slot to be overwritten is.
`_record_image_source_key` stamps the key after every real upload and **clears** it
for an unkeyed one, so a slot overwritten with different pixels cannot keep
claiming the old identity. The key table is reset everywhere the pool is
(`_destroy_image_source_pool`, the quarantine path, `shutdown`); the non-pooled
`alloc_buffer` lane stays unkeyed.

Two key producers, both computed ONCE per draw and never per frame:

* `inline_image_key` — for an image at or below `VK_IMAGE_INLINE_KEY_MAX_PIXELS`
  (64 words) the content IS cheap enough to be its own identity. This is what
  reaches the page's 76 one-pixel composites. It is honestly a bounded
  interpreted per-pixel loop (<= 64 iterations), and it REPLACES, on a hit, a
  `4 * N`-store staging pack plus an SFFI crossing. Above the bound the pixels
  are never touched: a per-frame digest of a large image would cost more than the
  upload it saves, which is exactly why large images need a producer key.
* `text_blit_image_key(text, color, font_size, w, h)` on the CPU text-blit path —
  that raster is a pure function of those five values, so the key walks the string
  rather than the raster. **On this page it fires zero times**: text takes the GPU
  atlas path (`font_composite n=18`), not the blit fallback. It is groundwork for
  the fallback lane, not part of the measured #6 win, and is stated as such here
  so no one reads the numbers below as its evidence.

`hint_image_key` is public so Draw-IR image producers can supply
`(node id, document generation)` for the large images without touching this file.

## Gate change

`check-web-vulkan-gpu-boundary-audit.shs` gained `--upload-mode u32|bytes`
(default `u32`, unchanged). It changes only HOW bytes cross the SFFI boundary,
never how many uploads or submits a frame performs, so a `bytes` run is
comparable on the COUNTS the gate gates on (ms are not comparable across modes).
It exists because an interpreter binary built before `rt_vulkan_copy_to_buffer_u32`
landed aborts the render with `unknown extern function`, which the gate could
previously only report as "no `[audit-frame]` record".

## Evidence

Binary `build/cargo-r2/release/simple`, `stat -f '%z %m'` = `39528776 1789199850`,
bracketed by the gate before AND after each run and identical on both sides.
`upload_mode=bytes` on both sides. Logs: `build/perf/gpu_audit_before_f26/`,
`build/perf/gpu_audit_after_f26/`.

| audit key | before | after |
|---|---|---|
| `uploads_per_frame` | **94** | **25** |
| `host_pixel_buckets` | `font_atlas_pack_u32_to_u8:16,image_pack_u32_to_u8:78` | `font_atlas_pack_u32_to_u8:16,image_pack_u32_to_u8:9` |
| `host_pixel_iterations` | 94 | 25 |
| `submits_per_frame` / `fence_waits` | 17 | 17 |
| `dispatches_per_frame` | 107 | 107 |
| `readbacks_per_frame` / `readback_bytes` | 2 / 5,472,000 | 2 / 5,472,000 |
| `atlas_full_repacks` | 5 | 5 |

69 of 78 image uploads per frame are gone (`image-upload-skipped` appears 69 times
in the after log). The 16 atlas uploads are the font lane's and are the floor
`uploads_per_frame` cannot go below here.

**Pixel equivalence.** The gate emits no PPM, so byte-comparing rendered images
was not available from it; the pixel oracle used instead is stronger than a count
and is stated rather than skipped: the `image-composite x= y= w= h= mode= rc=`
stream is **byte-identical** between the before and after logs (156 lines, `cmp`
clean), the `dispatch pipe= batched= rc=` stream has the identical md5
`ee57ca8890cd9f3d6dc48ac3acc1c4d2` on both sides, and `dispatches_per_frame` and
`readback_bytes` are unchanged. Every GPU operation that writes the framebuffer
is the same operation, in the same order, with the same result code; only the
host->device copies feeding them were elided.

**Sabotage (#6 / #5 counter validity).** With a `_flush_pending_compute_at("sabotage")`
forced after every image-composite dispatch, the gate goes red on BOTH counters:
`FAIL — 2 frame(s) audited, ... submits_per_frame=94 (>1)` with
`uploads_per_frame=94` and `image_pack_u32_to_u8:78` (the log carries exactly 156
`site=sabotage` flushes = 78/frame, one per composite). Reverting the sabotage
restores the table above. That both counters move is the point: it proves the
submit counter tracks real `vkQueueSubmit` calls rather than dispatches, AND that
the upload skip depends on slots surviving to the next frame — a flush per image
destroys the reuse, which is why the keyed path deliberately admits a slot that
is still pending. Recorded in `build/perf/gpu_audit_sabotage_f26/`.

**Specs.** `test/01_unit/lib/gpu/engine2d/vulkan_image_key_and_flush_site_spec.spl`
— 17 examples, device-free: key determinism and per-field separation for both
producers, the reserved zero key, the inline bound, arm/consume, **the key is
cleared even when the composite is rejected outright** (the wrong-pixels bug the
entry-consume ordering exists to prevent), fail-closed keyed lookup
(uninitialized backend / zero key / non-positive size), and flush-site
record-and-disarm. Existing Vulkan specs re-run green:
`vulkan_submitted_helpers_spec` 12/12, `backend_vulkan_text_fallback_spec` 2/2,
`vulkan_font_batch_admission_spec` 7/7.

## What is still open — #5, with the residual now attributed

Flush-site histogram from the after log (45 flushes over 2 frames + shutdown):

```
 22 site=untagged  pending_n=0  font_n=1     <- backend_vulkan_font.spl
  4 site=untagged  pending_n=0  font_n=2     <- backend_vulkan_font.spl
  2 site=untagged  pending_n=78 font_n=1     <- backend_vulkan_font.spl
  2 site=untagged  pending_n=1  font_n=1     <- backend_vulkan_font.spl
  4 site=read_pixels_with_source             <- owned here
  2 site=submit_batch                        <- owned here
  2 site=present                             <- owned here
  2 site=_flush_for_host_fallback pending_n=3
  3 site=shutdown
  2 site=untagged  font_n=0
```

**30 of 45 carry `font_n>0`: they are the font lane's, one per text run before
each atlas rewrite.** That flush is a genuine hazard, not waste —
`vulkan_sffi_copy_to_buffer(d_font_atlas, ..., 0)` is a host write to a buffer
that already-recorded dispatches read, so removing it without atlas versioning
would render earlier text runs with a later atlas. Closing it needs the
per-owner mirror / dirty-rect work tracked as audit defects #1 and #3
(`backend_vulkan_font.spl:1212-1276`), or a recorded copy+barrier primitive in
the runtime. Until then the honest cap for a text-bearing frame is
`1 + <font runs>`, and `submits == 1` is reachable today only for a text-free
frame.

The owned residual is small and named: ~4 flushes/frame, of which
`_flush_for_host_fallback` (1/frame, `pending_n=3`, from one of the
host-readback lanes at `backend_vulkan.spl:2493-2581`) is the only one that
flushes real recorded work. `read_pixels_with_source`/`present`/`submit_batch`
report `pending_n=0`. Reducing those is a separate change and is not claimed
here.

The presenter's two full-surface readbacks (audit #2) and its host-raster
pass-through (audit #4) are owned elsewhere and untouched.

## Landing: recorded test-tree divergence step-over

`check-test-tree-divergence-delta.shs cca466602e5 5ed4b04d364` returned
`PASS — 3209 pre-existing offender(s), 0 introduced by this range` (exit 0) over a
base that is itself RED (`FAIL — 3943 diverged vs 965 baselined; 26 mirror-only`).
Per `.claude/rules/vcs.md`, landing on a delta-PASS requires RECORDING the
pre-existing offender list rather than stepping over it silently. The list the
helper saved has **3943 entries** and is a property of `origin/main` at
`cca466602e5`, not of this change; it is reproducible byte-for-byte with
`sh scripts/check/check-test-tree-divergence.shs --ref cca466602e5`. First three,
for identification: `integration:app/add_remove_log_modes_spec.spl`,
`integration:app/app_mcp_intensive_spec.spl`,
`integration:app/brief_log_modes_spec.spl`. This change touches no file in either
duplicated test tree.

Other push guards, run in the foreground with `timeout 900` and the exit code read
into a variable on the following line: conflict-markers `rc=0`; tree-size
`PASS — 2 commit(s) checked ... 0 structural faults` `rc=0`; rt dual-implementation
ratchet `PASS — 2519 symbol(s) checked against 2519 baselined, 0 new, 0 stale`
`rc=0`.
