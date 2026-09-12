# The 8 full font-atlas repacks at 900x760 are NOT caused by two owners sharing one host mirror (macOS M4, 2026-09-12)

Status: **HYPOTHESIS REFUTED BY A CONTROLLED MEASUREMENT; the real root cause is
located and is in a file this lane does not own.** A per-owner mirror cache was
implemented anyway (it is correct, bounded, and proven pixel-safe), but it is
**inert on this page and must not be credited with a speed-up.**

## The hypothesis

`css-layout.html` at 900x760 pays 8 full 1,048,576-pixel atlas repacks
(`pack_full=8 pack_incremental=13`, `identity_changed=8`). The proposed cause was
that `VulkanBackend` keeps ONE host byte mirror keyed on the atlas owner
(`font_atlas_host_bytes` / `_identity` / `_generation`), so two font identities
alternating on one page evict each other's mirror and each forces the other's
full repack.

## What was built

`backend_vulkan.spl` gained `VulkanFontAtlasMirror {identity, generation, bytes}`
and `font_atlas_mirror_slots: [VulkanFontAtlasMirror]`, bounded by
`VULKAN_FONT_ATLAS_MIRROR_MAX = 4` (index 0 = least recently used, evicted
first). `backend_vulkan_font.spl` gained `_font_mirror_activate(owner,
entry_valid)`, called from `composite_font_batch` before the `can_increment`
decision: it parks the outgoing owner's bytes (only if the mirror was coherent at
function entry — a stale mirror is never parked, or a later switch would
resurrect it) and swaps the incoming owner's parked bytes back in.
`can_increment` now reads the POST-activation identity/generation.

All dirty-cell writes still go through `self.font_atlas_host_bytes`; a parked
slot's bytes are only ever replaced wholesale, never mutated in place (the
interpreter nested-place-clone landmine,
`doc/08_tracking/bug/interpreter_nested_place_mutation_clones_container_2026-09-12.md`).

`SIMPLE_VK_FONT_PER_OWNER_MIRROR=0` restores the single-mirror behaviour. It
exists as a **measurement control**, so before/after come from the same binary
and the same tree and cannot be contaminated by a rebuild.

## The controlled measurement

Binary `/Users/ormastes/simple/build/cargo-r2/release/simple`, same tree, same
page, `SIMPLE_2D_BACKEND=vulkan SIMPLE_VK_READBACK=native
SIMPLE_VK_IMAGE_UPLOAD=u32 SIMPLE_2D_BACKEND_STRICT=1
SIMPLE_EXECUTION_MODE=interpreter SIMPLE_VK_TIMING=1`, one run at a time.

| size | per-owner mirrors | pack_full | pack_incremental | identity_changed |
|---|---|---|---|---|
| 300x253 | off (control) | 2 | 3 | 2 |
| 300x253 | **on** | **2** | **3** | 2 |
| 900x760 | off (control) | 8 | 13 | 8 |
| 900x760 | **on** | **8** | **13** | 8 |

**Byte-for-byte identical counters at both sizes.** The hypothesis is refuted:
owner eviction is not what forces the full repacks.

PPM `cmp` clean at both sizes (control vs. per-owner) AND across all three
900x760 runs in this session (`before900` == `ctl900` == `after900`, byte for
byte) — which also re-confirms F19's determinism repair at this size. Further,
`SIMPLE_VK_FONT_SELFCHECK=1` at 300x253 reports `checks=3 bad_calls=0
bad_bytes=0` — the change is pixel-safe, it simply does nothing here.

## The actual root cause

`can_increment` requires `batch.atlas_generation ==
font_atlas_host_generation + 1`, and `atlas_generation` comes from **one GLOBAL
counter bumped once per dirty batch, shared by every atlas owner**. So whenever
two owners interleave, each owner's OWN sequence necessarily advances by 2 or
more while the global list stays contiguous — on an A,B,A,B page the list reads
`5 6 7 8` while A's own sequence is 5 -> 7. The `+1` test therefore fails **no
matter how many mirrors are cached**. Parking mirrors cannot repair a continuity
rule that the counter's shape makes unsatisfiable.

The evidence for that is the controlled measurement above, not the shape of the
printed list: with per-owner mirrors ON, `identity_changed=8` (the owners really
do interleave, and each switch really does find its parked mirror — the spec
cases below prove the swap-in works) and yet `pack_full` is unchanged at 8. The
gaps visible in the printed global list (`2 -> 4`, `13 -> 15`, `15 -> 17`) are a
DIFFERENT effect — batches that went to another backend surface, which the
continuity rule is also right to refuse — and are not the per-owner jumps.

The continuity rule itself is sound and must not simply be relaxed: a gap can
also mean a batch for THIS owner that this backend never saw (another surface's
backend compositing the same face inserts cells our mirror would miss), and
`dirty_rects` names only the current batch's insertions.

### The exact edit, in a file this lane does not own

`src/lib/gc_async_mut/text_layout/font_renderer.spl` must give
`FontRenderBatch` a **per-atlas-owner** sequence number alongside the global
`atlas_generation` — incremented once per dirty batch *for that owner's atlas* —
and `composite_font_batch` must test continuity on that field instead. Under a
per-owner sequence the alternating page becomes contiguous per owner, the
already-proven incremental repack applies, and the parked-mirror cache landed
here becomes the thing that makes it pay off. Without that field the cache is
dead weight on any interleaved page.

## The mechanism is proven to WORK, it just has nothing to do here

A cache that silently no-ops would produce the same identical counters, and the
interpreter's clone-on-mutate defects make that a real possibility for
`slots.push` / `slots.remove` on a class field. Five new device-free cases in
`test/02_integration/gpu/vulkan_font_atlas_incremental_repack_spec.spl` drive the
shipped `_font_mirror_activate` directly and rule it out: an owner parked behind
another owner comes back with its own bytes and generation intact; a mirror that
was stale at entry is never parked; the slot list is bounded at
`VULKAN_FONT_ATLAS_MIRROR_MAX` and evicts the least recently used owner;
re-activating the active owner parks nothing; an empty identity neither activates
nor parks. **19 examples, 0 failures** (14 pre-existing + 5 new).

## Timing is NOT reported as evidence

Wall clock on this host is unusable for a claim of this size: three 900x760 runs
of essentially the same work measured 226 s, 336 s and 584 s under concurrent
agent load. The counter table above is the evidence; the clock is not.

## Kept

The per-owner cache is kept rather than reverted: it is correct, bounded (4
slots), proven pixel-identical, and it is the half of the fix that cannot be
done in `font_renderer.spl`. It is explicitly NOT credited with any measured
improvement.
