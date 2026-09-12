# Vulkan page frame: the `site=untagged` flush is a NO-OP; the second submit is a mid-frame host round-trip

- Date: 2026-09-12
- Status: PARTIALLY RESOLVED — attribution fixed and made observable; the real
  second submit is a device-capability gap that is NOT closed here.
- Files: `src/lib/gc_async_mut/gpu/engine2d/engine.spl`,
  `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl`,
  `src/app/ui/chrome_showcase/gpu_boundary_audit.spl`
- Related: `vulkan_page_frame_17_submits_and_unkeyed_image_uploads_2026-09-12.md` (F30),
  `vulkan_font_atlas_midframe_flush_per_run_2026-09-12.md` (F32)

## The premise that was wrong

F30 recorded a Vulkan page frame as performing two submits — `site=submit_batch`
plus one `site=untagged` with `font_n=0` attributed to `engine.spl:3149,3181` —
and the follow-up work was scoped to removing that second submit.

The order trace falsifies it. Measured on `overview.html` at 900x760
(`build/perf/gpu_audit_before/overview_900x760_vulkan.log`, steady frame):

```
[vk-order] flush site=submit_batch          rc=1 pending_n=78 font_n=19
[vk-order] flush site=untagged              rc=1 pending_n=0  font_n=0
[vk-order] readback-entry                   pending_cmd=0 pending_n=0
[vk-order] flush site=read_pixels_with_source rc=1 pending_n=0 font_n=0
[vk-order] flush site=present               rc=1 pending_n=0  font_n=0
```

`pending_n=0` means `_flush_pending_compute_impl` returned at `cmd <= 0` —
before `vulkan_sffi_submit_and_wait_fence`. The untagged flush therefore
**submits nothing** and contributes nothing to `sffi_submit_and_wait`, the
bucket the audit gate counts as `submits_per_frame`. Removing it would not move
the number by one.

## Where the second submit actually comes from

Earlier in the SAME frame, on the same framebuffer (`fb=3`):

```
[vk-order] dispatch pipe=25/26 ... (3 dispatches enqueued)
[vk-order] image-composite x=6 y=12 w=888 h=384 mode=1 rc=1 fb=3
[vk-order] flush site=_flush_for_host_fallback rc=1 pending_n=3 font_n=0   <- REAL submit #1
[vk-order] readback-entry ...                                             <- readback #1 (full surface)
[vk-order] image-composite x=6 y=12 w=888 h=384 mode=0 rc=1 fb=3          <- host result uploaded back
... rest of the frame ...
[vk-order] flush site=submit_batch rc=1 pending_n=78                      <- REAL submit #2
```

A blend that has no device pipeline forces a **mid-frame host round-trip**:
submit the batch, read the whole surface back, composite on the host, upload the
result. That is the second submit AND the second readback (`readbacks_per_frame=2`).
`_flush_for_host_fallback` returns `true` on status 1 without
`mark_cpu_fallback`, so the census still reports `cpu_fallback_count=0` while a
full host round-trip happened — the gate saw it only as a readback count.

Closing it means implementing that blend on the device (shader work in the
`draw_ir_adv`/GLSL lane), which is out of this lane's file scope. It is NOT
fixed here, and the gate's `submits > 1` / `readbacks > 1` invariants are
deliberately left unchanged: loosening the gate to admit the exact interaction
it exists to refuse would normalize the defect.

## What this change does

1. **Attribution.** `engine.spl`'s two pre-readback flushes now tag themselves
   `engine.read_pixels` / `engine.read_pixels_with_source` instead of reaching
   the untagged entry point, and `_flush_for_host_fallback` now carries its
   reason in the tag (`_flush_for_host_fallback:<reason>`). No frame can again
   be read as "an anonymous font-lane submit" when it is neither.
2. **Pixel-level observability (F32's sabotage gap).** The audit gate now
   reports `frame_digest=` — FNV-1a/32 over the final readback words in order,
   computed from the pixels the audit already holds, never from a second
   readback. Every other key it reports is a COUNT, so a sabotage that leaves
   the op counts identical and changes only what the ops wrote was invisible.
   A one-pixel change, or two pixels swapped, flips the digest
   (`test/01_unit/app/ui/gpu_boundary_audit_spec.spl`, 22/22).
   A log predating the key reports `unavailable`, never a fabricated value.
3. **Host round-trip attribution in the gate.** `host_fallback_submits=` and
   `host_fallback_reasons=` name the flushes that really submitted
   (`pending_n>0`); no-op flushes are excluded by construction.

## Evidence

Binary `/Users/ormastes/simple/build/cargo-r2/release/simple` `39528776 1789199850`
(identity bracketed by the gate itself, unchanged across both runs).
Env: `SIMPLE_EXECUTION_MODE=interpreter SIMPLE_2D_BACKEND=vulkan
SIMPLE_VK_READBACK=native SIMPLE_VK_IMAGE_UPLOAD=u32 SIMPLE_VK_RECT_UPLOAD=u32`,
page `overview.html` at 900x760, 2 frames.

Before and after are the same on the counters, as the analysis above predicts:
`submits_per_frame=2`, `readbacks_per_frame=2`, `fence_waits=2`. The change is
what the log now SAYS about them, plus the digest. The gate verdict stays FAIL
for `host_pixel_iterations` (F32's lane), `readbacks_per_frame` and
`submits_per_frame` — honestly red, not gated green.

## Measured after (same binary, same env, `overview.html` 900x760)

```
submits_per_frame=2        readbacks_per_frame=2      fence_waits=2
frame_digest=782b75f1
host_fallback_submits=1    host_fallback_reasons=blur-host-readback
FAIL — 2 frame(s) audited, violated: host_pixel_iterations=15 (>0):
       font_atlas_pack_u32_to_u8:15; readbacks_per_frame=2 (>1); submits_per_frame=2 (>1)
```

The counters are unchanged, exactly as the no-op analysis predicts. What is new
is that the frame now NAMES its extra submit: `blur-host-readback`
(`backend_vulkan.spl:2658`) — a CSS blur with no device pipeline. That is the
one open item, and it is shader work in the `draw_ir_adv`/GLSL lane, not this
one. The frame also now carries a pixel digest, so a sabotage that leaves those
counters alone is observable.

## Landing note

`check-test-tree-divergence-delta` PASS — 3209 pre-existing offender(s), 0
introduced by this range (base verdict FAIL: 3943 diverged vs 965 baselined;
list saved by the helper at
`$TMPDIR/test_tree_divergence_preexisting.txt`). `check-guard-wiring` FAIL on
ONE pre-existing new unwired guard, `check-blit-spirv-pinned.shs`, which this
range does not touch and does not own. Conflict-markers, tree-size and
rt-dual-implementation ratchet all PASS.
