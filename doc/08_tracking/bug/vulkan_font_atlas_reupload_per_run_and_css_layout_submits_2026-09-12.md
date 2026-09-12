# Vulkan font atlas re-uploaded per text run; css-layout.html submits 3x per frame

Status: FIXED 2026-09-12
Gate: `scripts/check/check-web-vulkan-gpu-boundary-audit.shs`
Binary: `build/cargo-r2/release/simple` (identity `39528776 1789199850`, unchanged across every run below)

## (a) The atlas was copied to the device once per text run

Every run that inserts a glyph bumps the owner's published `atlas_owner_sequence`,
so the slot plan is `WRITE_IN_PLACE`, and that branch copied the FULL 1024x1024
atlas (4 MiB) each time -- ~15 copies, ~60 MB, on a page with one atlas. All but
the last are dead: within a flush the atlas only GROWS (cells are inserted, never
relocated -- the invariant `WRITE_IN_PLACE` already rests on), so the final state
is a superset of every intermediate one, and every dispatch that reads the atlas
is recorded into the SAME not-yet-submitted command buffer.

Fix: the typed (`u32`) lane PARKS the copy (`font_atlas_deferred_*` on the
backend) and drains it in `_flush_pending_compute`, immediately before the
submit. A park aimed at a different buffer drains the previous one first, so the
count is bounded by distinct slots written, never by runs. The byte fallback lane
is unchanged. Release paths (`_font_atlas_release_slots`, backend teardown)
DISCARD a park rather than drain it -- the buffer it names is being freed.
A failed drain poisons only that slot (owner `""`, sequence -1) and marks
`atlas-deferred-upload-failed`.

## (b) css-layout.html reported submits_per_frame=3

Two independent causes, both found with the tagged `SIMPLE_VK_ORDER_TRACE=1`
flush trace:

1. **A zero-area opaque rect.** `_draw_rect_filled_impl`'s device arm had no
   `w <= 0 or h <= 0` guard (the alpha and masked arms did), so `(0 + 15) / 16`
   gave 0 workgroups. `_enqueue_framebuffer_compute` rejects that with a bare 0
   and no trace, and `_dispatch_framebuffer_checked` read the 0 as the measured
   M4 bind-chain flake: it flushed the whole pending batch (an extra SUBMIT),
   retried with the SAME invalid arguments, failed identically, and latched the
   CPU fallback. Two such rects per frame. Fixed at the call site, and
   generally: `_dispatch_framebuffer_checked` now rejects degenerate arguments
   up front (`dispatch-reject` trace, no flush, no futile retry).

2. **One owner holding two slots.** A relocating `WRITE_FRESH` moved an owner to
   a new slot while the OLD slot kept the owner's name at a stale sequence.
   `_font_atlas_slot_index` returns the first match, so every later run for that
   owner found the stale slot, could neither reuse nor write in place, and
   eventually exhausted the table into a `FLUSH_THEN_WRITE` -- the third submit.
   A successful write now disowns every other slot naming that owner.
   `VULKAN_FONT_ATLAS_SLOT_MAX` 4 -> 8 (an "owner" folds point SIZE into its
   identity, so css-layout presents five owners from two families); the env
   measurement control accepts 1..8.

## Evidence (gate before / after, same binary)

| page | metric | before | after |
|---|---|---|---|
| overview.html | uploads_per_frame | 23 | **13** |
| overview.html | upload_ms | 43 | **19** |
| overview.html | submits_per_frame | 1 | 1 |
| overview.html | frame_digest | a15c50cd | **a15c50cd** |
| overview.html | verdict | PASS | PASS |
| css-layout.html | uploads_per_frame | 47 | **25** |
| css-layout.html | upload_ms | 57 | **32** |
| css-layout.html | submits_per_frame | **3** | **1** |
| css-layout.html | fence_waits | 3 | **1** |
| css-layout.html | frame_digest | 743c2081 | **743c2081** |
| css-layout.html | verdict | FAIL | **PASS** |

`frame_digest` identical on both pages is the pixel oracle: the op counts fell
and the rendered words did not move. `cpu_fallback_count=0` on both.

## Specs (interpreter, `simple run`)

Green: `backend_vulkan_font_atlas_slot_plan_spec` 12/12,
`backend_vulkan_font_typed_upload_spec` 4/4,
`backend_vulkan_font_quad_partition_spec` 7/7,
`backend_vulkan_drawing_spec` 44/44.

PRE-EXISTING RED, not caused by this change: `backend_vulkan_blend_cpu_parity_spec`,
`backend_vulkan_device_glass_blur_spec`, `backend_vulkan_font_spec`,
`backend_vulkan_rect_batch_one_dispatch_spec` all report `outcome=ERROR
executed=0` from an unresolved `use gpu.engine2d.engine.{Engine2D}` (E1034, a
non-`std.`-prefixed import in the SPEC file). Unrelated to these files.

## Still open

`uploads_per_frame` is ~5/frame for overview and ~7/frame for css-layout rather
than one-per-changed-owner: the frame performs several flushes (font-lane,
read_pixels, present), and each drains at most once, so the residual is
flush-count x owner-switches, not per-run. Collapsing the per-frame flush count
itself is a separate lane.
