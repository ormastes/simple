# The 8 full font-atlas repacks at 900x760 are NOT caused by two owners sharing one host mirror (macOS M4, 2026-09-12)

> **FOLLOW-UP 2026-09-12 (F22) — the named fix was premised on `atlas == face`,
> and the code says otherwise. Read this before implementing the "exact edit"
> section below, which is now superseded.**
>
> The section "The exact edit, in a file this lane does not own" proposed a
> per-owner sequence on `FontRenderBatch` *alone*. That is not sufficient and,
> shipped alone, is **unsound**:
>
> * `Engine2D` holds exactly ONE `FontRenderer` (`font_owner.active[0]`,
>   `engine.spl:344`), and that renderer owns exactly ONE atlas buffer.
> * A face switch called `_reset_font_atlas`, which **wipes** the atlas
>   (`atlas_pixels = [0u32; 1024*1024]`, all index arrays cleared). So on an
>   A,B,A,B page, returning to A did not "come back to A's atlas" — it came
>   back to a *zeroed* atlas and re-rasterised A's glyphs from scratch.
> * With a per-owner sequence but no park, `can_increment` would have become
>   true against a parked mirror holding A's OLD pixels, while the truth is a
>   fresh atlas carrying only this run's re-inserted cells. `dirty_rects` names
>   only the latter, so the mirror would keep stale pixels outside them and
>   `SIMPLE_VK_FONT_SELFCHECK` would go red. F21's green selfcheck is no
>   evidence to the contrary: `can_increment` never fired, so the per-owner
>   mirror was never once compared against truth.
>
> **The sound fix is the pair**, and both halves landed together:
>
> 1. **Producer-side park** (`font_renderer.spl`): `FontAtlasPark` +
>    `_switch_font_atlas`, replacing the bare wipe on the two identity-switch
>    guards. A face switch now parks the outgoing atlas (pixels, all nine index
>    arrays, cursors, sequence) keyed by `(font_identity, face_generation)` —
>    the same pair the switch tests, and the same key F21's mirror uses — and
>    restores the incoming owner's if parked. Bounded at
>    `FONT_ATLAS_PARK_MAX = 4`, LRU-evicted; an evicted owner falls back to the
>    wipe, i.e. to the previous behaviour. The active owner never holds a live
>    slot (it is removed on restore, re-added on switch), so no two live places
>    alias the same arrays. The overflow/error resets are left as wipes — they
>    are genuine invalidations, not switches.
> 2. **`FontRenderBatch.atlas_owner_sequence`** (`font_types.spl` — note the
>    batch lives there, not in `font_renderer.spl`, and `common/text_layout/`
>    is only a facade). Advanced by exactly 1 per dirty batch on that atlas,
>    parked and restored with it, and **seeded from the globally-monotone
>    counter on every reset** so a wiped owner can never reuse a value a
>    consumer's mirror still holds. `-1` = producer publishes none.
>
> Consumer side: the decision moved out of `composite_font_batch` into the
> device-free free function `vulkan_font_mirror_continuity`
> (`backend_vulkan_helpers.spl`), which returns one of three outcomes.
> `VK_FONT_MIRROR_ALREADY_TRUTH` is the third and is not an optimisation of the
> incremental path: a returning owner whose glyphs are all cached emits **no**
> dirty cells, so its sequence does not move, and under a plain `+1` rule that
> is a full repack of an atlas the mirror already matches exactly.
> `VulkanFontAtlasMirror` parks `owner_sequence` alongside `generation`; the
> device-side `font_atlas_generation` is deliberately NOT parked, so the
> re-upload still happens after a restore. With no sequence published the old
> global `+1` rule still applies unchanged.
>
> Measurement control: `SIMPLE_FONT_ATLAS_PARK=0` restores the bare wipe, so
> before/after come from one binary and one tree, matching
> `SIMPLE_VK_FONT_PER_OWNER_MIRROR=0`'s purpose.
>
> Spec: `test/02_integration/gpu/vulkan_font_atlas_incremental_repack_spec.spl`
> **27 examples, 0 failures** (19 pre-existing + 8 new), including the A,B,A,B
> interleave (2 full, 2 incremental), its SABOTAGE twin on the global counter
> (4 full — the pre-fix behaviour, visibly worse), the no-dirty-cells case, a
> per-owner gap that repacks only that owner, and a producer round-trip proving
> a parked atlas returns with its pixels and its sequence intact.
>
> ### F22 RESULT: the sequence works, and `pack_full` at 900x760 is STILL 8 — because the page has 8 owners, not 2
>
> Measured on a privately-built binary (`37568056 1789199216`; the shared one
> was replaced mid-session by a partial build that cannot run this lane at all).
> `pack_full=8 pack_incremental=13 identity_changed=8` — **unchanged**, and
> `SIMPLE_VK_FONT_SELFCHECK=1` reports `bad_calls=0 bad_bytes=0`.
>
> The per-batch decision notes say why, and they say it is not a continuity
> failure. Across the frame: **26 `continuity=1`** (incremental) and **16
> `continuity=0`** (full). Of the full ones, the 8 that matter carry
> `owner_match=false len_match=false` — the incoming owner had **no parked
> mirror to find**, so the bytes were empty and there was nothing to be
> continuous with. Every other decision is `owner_match=true len_match=true`,
> and the published sequences are exactly contiguous within an owner
> (`seq=7 host_seq=6`, `8←7`, `9←8`, … `15←14`). The two `host_seq=-1` entries
> (`seq=3`, `seq=18`) are cold starts.
>
> So the per-owner sequence is doing its job wherever an owner recurs. What
> defeats it on this page is that **the producer keeps WIPING the atlas**, and
> the sequence log says so unambiguously.
>
> `_reset_font_atlas` draws from the globally-monotone counter **twice** (once
> for `atlas_generation`, once to seed `atlas_owner_sequence`) and the next
> dirty batch adds 1, so a wipe has a signature: a **+3 jump** in the published
> sequence. Every cold entry in the frame follows exactly that jump —
> `15 -> 18`, `18 -> 21`, `22 -> 25`, `25 -> 28`, `30 -> 33`, `33 -> 36`. A
> relabel of a shared atlas (the `-2` shaped path rewriting `atlas_font_identity
> = dependencies`) does NOT reset and would show `prev + 1`. It does not appear.
> **The atlas is being wiped, not merely renamed** — which also rules out the
> first reading of this result, that the owner identity string simply grows.
>
> The consumer-side park is meanwhile demonstrably alive: `seq=21 host_seq=15`
> and `seq=33 host_seq=25` are mirrors that WERE found and swapped back in
> (`owner_match=true`) — and then failed continuity anyway, because the producer
> had wiped underneath them.
>
> ### TRACED (same run, `SIMPLE_FONT_ATLAS_TRACE=1`): the park key is written under one name and looked up under another — an OPEN DEFECT in this change
>
> The trace settles it and it is not any of the three candidates below, nor the
> "identity string grows" reading. Over the 900x760 frame:
>
> * `_switch_font_atlas` fires **5 times**, `reset-2` **0 times** — so the
>   shaped-run bypass (candidate b) never runs on this page.
> * The incoming keys are only **TWO distinct values**, alternating:
>   `…;axes=wght=100|face-generation=1` (3x) and
>   `…;axes=wght=400,wdth=100|face-generation=1` (2x). **The brief's A,B,A,B
>   interleave is real**, and the owner axis is the variable-font weight.
> * Parking is genuinely happening: the slot count grows `0 -> 1 -> 2` and then
>   holds at 2, i.e. both owners are resident and nothing is LRU-evicted
>   (candidate c is out; `FONT_ATLAS_PARK_MAX = 4` is not the constraint).
> * And yet **every one of the 5 switches reports `reset`. Zero restores.**
>
> Two parked slots, two repeating lookup keys, no hit: the key STORED is not the
> key SEARCHED. The park stores
> `font_atlas_park_key(self.atlas_font_identity, self.atlas_face_generation)` —
> mutable fields that other paths rewrite between switches (the shaped `-2`
> branch assigns `self.atlas_font_identity = dependencies` and the sentinel
> generation `-2`, and the overflow resets reassign both). The lookup asks for
> the incoming `(font_identity, face_generation)`, which the trace shows is
> `(…wght…, 1)`. A slot filed under `(dependencies, -2)` can never answer it.
>
> **This is a defect in the F22 change, not in the pre-existing code**, and it is
> why the park is inert here: the mechanism is right, the key is wrong. It is
> recorded rather than blind-patched because confirming the fix costs another
> ~8-minute 900x760 run and the candidate correction (capture the outgoing key
> at the moment the owner becomes active, instead of re-deriving it from fields
> other paths mutate) must be verified, not assumed. Until then the park is
> bounded, pixel-safe and does nothing — exactly F21's status, one layer in.
>
> **Superseded candidate list** (kept for the reasoning trail; (b) and (c) are
> now refuted by the trace above, (a) is refined into the key-mismatch defect): (a traced run is queued;
> `SIMPLE_FONT_ATLAS_TRACE=1` now prints `restore`/`reset`/`reset-2` with the
> key):
> (a) `_switch_font_atlas` finds no park because the KEY churns — the text path
> takes `face_generation` from `active_rasterizer.cache_identity_generation()`
> (`:2160`), which may move per size/weight, minting a fresh key each time;
> (b) the shaped-run guard `if self.atlas_face_generation != -2:
> _reset_font_atlas(-2, …)`, which **bypasses the park entirely** on every
> text->shaped transition while the text side parked under `(dependencies, -2)`;
> (c) LRU eviction at `FONT_ATLAS_PARK_MAX = 4`.
> Whichever fires 8 times is the root cause, and the next lever differs per
> branch (stabilise the generation / route the `-2` guard through the park /
> raise the bound). Recording the candidates instead of guessing one.
>
> **The brief's target (`pack_full == distinct owners == 2`) was not reachable
> on this page** as long as the producer wipes 6-8 times per frame, whatever the
> continuity rule says.
>
> **What is and is not proven.** Proven on the live page: the sequence rule's
> incremental path, 26 `continuity=1` repacks compared byte-for-byte against a
> full pack with `bad_bytes=0`. NOT proven on the live page: the park (it
> restored twice but no restore ever reached a successful incremental, so no
> restored mirror has been compared against truth) and `ALREADY_TRUTH`
> (`continuity=2` fired **0** times here). Both are spec-proven only. F21 had
> already selfchecked 13 incremental repacks at this size, so the live
> selfcheck evidence is an extension of that, not a first.
>
> The park and sequence are kept — correct, bounded, and the prerequisite for
> whichever wipe fix follows — and are explicitly **not** credited with any
> `pack_full` reduction on this page.

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
