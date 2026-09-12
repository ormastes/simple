# Vulkan font lane flushes once per text run, so a page frame costs 17 submits

- **Filed**: 2026-09-12
- **Area**: `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font.spl`,
  `backend_vulkan_helpers.spl`, `backend_vulkan.spl` (field/init/teardown only)
- **Status**: FIXED — 17 submits/frame -> 2 on the catalog overview page
- **Predecessors**: F16 (dirty-rect incremental repack), F24 (per-owner mirror
  park + per-owner continuity), F30 (submit attribution)
- **Successors / not this lane**: F29 (presenter, `readbacks_per_frame=2`),
  F31 (`backend_vulkan.spl` blend/glsl)

## Symptom

A text-bearing page frame submits and fence-waits 17 times against an invariant
of 1. F30 attributed 30 of a two-frame run's 45 flushes to
`backend_vulkan_font.spl`, and correctly identified them as a genuine
read-after-write hazard rather than gratuitous synchronisation: the lane held
exactly ONE device atlas buffer (`d_font_atlas`), so before any host write to it
the already-recorded dispatches that read it had to be submitted and waited. The
honest cap under that design was `1 + font runs`.

Measured before, `scripts/check/check-web-vulkan-gpu-boundary-audit.shs --page
examples/06_io/ui/web_catalog/overview.html --width 900 --height 760
--upload-mode u32`:

```
submits_per_frame=17
fence_waits=17
dispatches_per_frame=107
atlas_full_repacks=4
host_pixel_iterations=16 (font_atlas_pack_u32_to_u8:16)
FAIL — 2 frame(s) audited, violated: ... submits_per_frame=17 (>1)
```

## Why the obvious fix does not work

Double- or ring-buffering the atlas round-robin does NOT reach 1 submit. Run 1
takes slot A, run 2 slot B, run 3 finds both referenced by unsubmitted
dispatches and flushes anyway. At depth `d` the cost is `1 + runs/d` — with ~10
font runs per frame and depth 2 that is ~6 submits, not 1. Depth is the wrong
axis.

## Root cause

The buffer was keyed on nothing. One device buffer served every font owner, so
*any* content change — including merely switching back to a face whose atlas the
device had already held — rewrote it and therefore had to flush first.

Two facts F16/F24 had already established make almost every one of those writes
unnecessary:

1. When an owner's parked atlas is restored unchanged (continuity
   `ALREADY_TRUTH`), the device slot for that owner still holds exactly those
   bytes. No write is needed **at all** — so no flush. On an alternating A,B,A,B
   page this is most runs.
2. An `INCREMENTAL` batch writes only cells this batch inserted. Every cell a
   recorded dispatch reads keeps a byte-identical value, so the write is not a
   hazard even though it is a full-buffer `copy_to_buffer`.

Note that the producer's own wipe path makes (1) sound: `_reset_font_atlas`
re-seeds `atlas_owner_sequence` from the same globally monotone counter it drew
the generation from, so a wiped atlas can never present a sequence a stale slot
still holds (it is always at least +2 past it). Equal published sequence
therefore means equal bytes.

## Fix

Key the device atlas on the ATLAS OWNER: a small table of device buffers
(`VULKAN_FONT_ATLAS_SLOT_MAX = 4`), each recording the owner and the published
`atlas_owner_sequence` its bytes incorporate, plus whether a dispatch recorded
into the current unsubmitted command buffer reads it.

The whole decision is one pure function, `vulkan_font_atlas_slot_plan`
(`backend_vulkan_helpers.spl`), lifted out of the composite so the submit-count
invariant is testable without a device:

| plan | when | flush? |
|---|---|---|
| `REUSE_NO_WRITE` | slot holds this owner at this exact published sequence | no — and no upload, no pack |
| `WRITE_IN_PLACE` | `INCREMENTAL` and the slot holds exactly the sequence the mirror was at before this batch (`slot_seq == host_seq_before`, `batch_seq == host_seq_before + 1`); or nothing recorded reads the slot | no |
| `WRITE_FRESH` | this owner has no slot, or a relocating write can take an unreferenced/new slot | no |
| `FLUSH_THEN_WRITE` | a relocating (`FULL`) write into a referenced slot with no spare | yes — the only flush the lane still owes |

Every branch is fail-closed: an unpublished sequence (-1) matches nothing, so it
can never take a no-write or in-place path. `referenced` flags are cleared by
`_clear_pending_compute_state`, which runs on every flush return path including
the failure ones. A failed upload poisons only its own slot.

An atlas DIMENSION change still flushes unconditionally and releases every slot
— the buffers are the wrong size and nothing can be reused. That fires at most
once per surface resize, not once per text run.

F19's sub-batch partition and F24's park/continuity semantics are untouched; the
mirror still follows the slot that was last written (`_font_mirror_activate` was
hoisted above the slot decision because the plan needs the continuity verdict,
and on a no-write run nothing is written, so the invariant is preserved).

### Measurement control

`SIMPLE_VK_FONT_ATLAS_SLOTS=1` collapses the table to one slot, reproducing the
pre-fix behaviour exactly, so before/after evidence can come from ONE binary and
ONE tree and cannot be contaminated by a rebuild. Values outside 1..4 degrade to
the default rather than to one slot.

## Evidence

Binary `/Users/ormastes/simple/build/cargo-r2/release/simple`
(`stat -f '%z %m'` = `39528776 1789199850`, unchanged across every run below —
the audit gate asserts this itself via `identity_before`/`identity_after`).

overview.html, 900x760, `--upload-mode u32`:

| counter | before | after |
|---|---|---|
| `submits_per_frame` | 17 | **2** |
| `fence_waits` | 17 | **2** |
| `atlas_full_repacks` | 4 | 4 (not worse than F24's 5) |
| `dispatches_per_frame` | 107 | 107 |
| `host_pixel_iterations` | 16 | 15 |
| `readbacks_per_frame` | 2 | 2 |

css-layout.html, 900x760, `--upload-mode u32`:

| counter | `SLOTS=1` control | default |
|---|---|---|
| `submits_per_frame` | 8 | **4** |
| `fence_waits` | 8 | **4** |
| `atlas_full_repacks` | 5 | 5 (equal to F24's 5) |

Read the css-layout control as a LOWER BOUND on the pre-fix cost, not as the
pre-fix cost: at depth 1 the `REUSE_NO_WRITE` rule still fires whenever the sole
slot happens to hold the right owner, so depth 1 is strictly better than the old
design, which had no such rule at all. The honest pre-fix number measured
against the actual pre-fix tree is the overview page's 17. The control's value
is that it moves in the right direction from the same binary and tree.

### Attribution of the 2 remaining submits — measured, not assumed

The gate arms `SIMPLE_VK_ORDER_TRACE=1`, and every submit this backend performs
comes from exactly one `_flush_pending_compute`, tagged with its call site.
Across the 2-frame after-run:

```
2 flush site=submit_batch              rc=1 pending_n=78 font_n=19
2 flush site=untagged                  rc=1 pending_n=0  font_n=0
2 flush site=_flush_for_host_fallback  rc=1 pending_n=3  font_n=0
4 flush site=read_pixels_with_source / 2 present / 3 shutdown   (outside the frame body)
```

Per frame the two submits are `submit_batch` (the legitimate single
end-of-frame submit, carrying all 19 font descriptors) and one `untagged` with
**`font_n=0`** — i.e. no font work pending, so it is not an atlas transition.
The untagged font-lane site in this file (`font_oracle_mode`, line 1185) is not
active in this run; the untagged callers are `engine.spl:3149,3181`. **Zero
atlas-transition flushes remain**, which the `atlas_forced=` counter now on the
order-trace line confirms independently. Removing the residual submit is F29's
work, not this lane's.

The gate still reports FAIL, honestly: the two invariants it names besides
submits — `readbacks_per_frame=2` and `host_pixel_iterations=15` — belong to
F29 (presenter) and the mirror-pack lane (F16), not to this one.

### Pixel identity

- Frame `sha256` digests in the order trace are byte-identical between the
  pre-fix tree and the fixed tree.
- All 8 `chrome_showcase` PPMs at 900x760 (`animation`, `css-layout`,
  `css-paint`, `evidence`, `forms-media`, `html`, `overview`, `tab-bar`) are
  `cmp`-identical between `SIMPLE_VK_FONT_ATLAS_SLOTS=1` and the default.
- `SIMPLE_VK_FONT_SELFCHECK=1` over the same render: clean (0 mirror
  mismatches, 0 `atlas-slot-owner-mismatch`), and its PPM is identical to the
  non-selfcheck one.

Specs: `backend_vulkan_font_atlas_slot_plan_spec` 12/12 (new; counter oracle for
the submit count, the depth-1 control, and the overflow case),
`vulkan_font_atlas_incremental_repack_spec` 30/30,
`backend_vulkan_font_quad_partition_spec` 7/7,
`backend_vulkan_rect_batch_typed_upload_spec` 8/8.

## Known limits

- The typed `[u32]` atlas upload path (`SIMPLE_VK_FONT_UPLOAD=u32`) was NOT
  added. It is not on the submit-count path — the atlas host write goes through
  `vulkan_sffi_copy_to_buffer`, and `rt_vulkan_copy_to_buffer` already stages
  through a transfer command of its own regardless of payload shape. Recorded
  here as a follow-up rather than folded in to keep this change to one claim.
- `host_pixel_iterations` is barely moved (16 -> 15): full mirror packs are an
  F16 concern, not a submit-count one.
- The plan proves no relocating write races a recorded dispatch. It does not
  prove the atlas pixels are correct; that stays with
  `SIMPLE_VK_FONT_SELFCHECK=1` and the incremental-repack spec, and a selfcheck
  slot-owner assertion (`atlas-slot-owner-mismatch`) was added to catch a
  wrong-slot bind that a pixel oracle could miss.

- **The sabotage half is only PARTLY demonstrated, and this is stated rather
  than implied.** `SIMPLE_VK_FONT_ATLAS_SABOTAGE=same-slot` forces every run
  onto slot 0 AND onto the no-write outcome. It provably takes effect — under
  it, overview's `atlas_full_repacks` falls 4 -> 1 and
  `host_pixel_iterations` 16 -> 1, because uploads stop happening. What was NOT
  produced in this session is a pixel-level RED from it: the audit log carries
  no frame-pixel digest (its `sha256=` fields are font identities), and the
  `chrome_showcase` PPM path does not appear to route text through this
  composite — all 8 PPMs stayed identical under sabotage, which is evidence
  about that path, not about the guard. The `atlas-slot-owner-mismatch`
  assertion is therefore present and reachable but has not been observed
  firing. A follow-up needs a pixel oracle on a page with two font owners that
  provably goes through `_composite_font_batch`.
  A weaker first attempt — pointing every owner at slot 0 WITHOUT forcing the
  plan — was absorbed entirely by the slot logic (it saw the sequence mismatch
  and took a fresh slot), leaving all 8 PPMs identical. That negative result is
  recorded because it is the reason the knob forces both halves.
