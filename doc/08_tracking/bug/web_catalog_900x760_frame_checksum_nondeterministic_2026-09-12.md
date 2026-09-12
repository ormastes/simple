# The css-layout catalog page renders NON-DETERMINISTICALLY at 900x760 on the Vulkan lane (macOS M4, 2026-09-12)

Status: **OPEN, pre-existing, not caused by any change in this lane.** Filed
because it silently invalidates frame-checksum and PPM comparison as a
before/after oracle at this size — and has already caused one correct patch to
be backed out.

Binary bracketed identical on every run: `/Users/ormastes/simple/build/cargo-r2/release/simple`,
`stat -f '%z %m'` = `39368072 1789171430`. Page
`examples/06_io/ui/web_catalog/css-layout.html` at 900x760,
`SIMPLE_2D_BACKEND=vulkan SIMPLE_VK_READBACK=native SIMPLE_2D_BACKEND_STRICT=1
SIMPLE_EXECUTION_MODE=interpreter`, one run at a time. Logs:
`build/perf/vk_attr_2026-09-12/` (gitignored).

## The observation

Seven runs across four source variants produced **three distinct whole-frame
checksums**, and the variants do not partition them:

| run | product logic | checksum |
|---|---|---|
| `vk900_before` | no host mirror | 2936851417192293 |
| `vk900_after` | mirror, invalidate inside dirty branch | 2936851411469080 |
| `vk900_after_rep` | *identical tree to the row above* | 2936851411469080 |
| `vk900_fix2` | + invalidate at function entry | 2936851404759230 |
| `vk900_fix3` | + require generation continuity (strictly stricter) | 2936851411469080 |
| `vk900_diag` | fix3 + a READ-ONLY self-check | **2936851417192293** |

Two facts kill every "the change moved the pixels" reading:

1. **A strictly stricter variant (`fix3`) returned a looser variant's value**,
   and `pack_full=8 pack_incremental=13` was identical across all of them — the
   guard conditions never changed which batches took which path.
2. **`vk900_diag`, which runs the mirror ACTIVELY (13 incremental repacks),
   produced exactly the no-mirror baseline checksum.** A change cannot both
   alter pixels and reproduce the unaltered pixels.

## The incremental repack is independently PROVEN correct

`SIMPLE_VK_FONT_SELFCHECK=1` compares the host mirror against a full pack of the
same atlas after every incremental repack — the ground truth, computed by the
same function the full path uses. Result on the 900x760 page:

```
font_mirror_selfcheck checks=13 bad_calls=0 bad_bytes=0 first=[]
```

**13 incremental repacks, zero mismatching bytes.** The per-composite decision
log also shows the guard behaving exactly as designed: every incremental repack
has `host_gen == gen - 1` with `owner_match=true`, and every full repack is
caused by `owner_match=false`, i.e. a genuine font-face change.

So the mirror is byte-exact, and the frame checksum still moves. The divergence
is downstream of the font atlas entirely.

## Why this matters beyond this lane

`doc/08_tracking/bug/web_catalog_vulkan_lane_raster_term_2026-09-12.md` records
that F14's corner-sprite coalescing was measured at **-13.7%** and then **held
back** because "at 900x760 the frame checksum MOVED (2936851399036017 ->
2936851411469080)". That value, `2936851411469080`, is one of the three this
page produces on its own with no coalescing anywhere in the tree. **A correct
optimisation was very likely backed out on noise.** Anyone re-measuring that
patch must use a different oracle.

## What to use as an oracle instead, until this is fixed

- 300x253 IS stable: every run in this lane produced `325932497106919` and
  byte-identical PPMs. Use it for pixel equality.
- At 900x760, compare against an INVARIANT the change is supposed to preserve
  (the mirror self-check above), not against a whole-frame checksum.

## Where to look

Nondeterminism appears at 900x760 and not at 300x253, and the two differ in
exactly the offscreen-group path: 900x760 reports `image=2 readbacks=3`, while
300x253 reports `image=0 readbacks=1`. That is also where the 900x760 time goes
— `_draw_image_composite_native` is 544 s of a 789 s frame with a single call
reaching 179 s (see
`doc/10_metrics/ui/web_catalog_vulkan_per_op_attribution_macos_2026-09-12.md`).
A composite whose cost varies by two orders of magnitude between calls and a
frame whose pixels vary between runs are plausibly the same defect: a
flush/fence or descriptor-pool reuse whose ordering is not pinned. Not
confirmed — no probe in this lane measured it.

---

## UPDATE 2026-09-12 (diagnosis lane): it is RASTER, and it is TWO PIXELS

The five archived 900x760 PPMs (`build/perf/vk_attr_2026-09-12/*.ppm`, source
worktree `agent-ade87e8937ee40e79`) were byte-diffed pairwise. The whole
"three distinct checksums" phenomenon is **1 or 2 differing pixels out of
684,000** — nothing else on the frame ever moves:

| pair | differing pixels | bbox |
|---|---|---|
| before vs after / after_rep / fix3 | **1** | (89,392) |
| before vs fix2 | **1** | (474,560) |
| after vs fix2 | 2 | (89,392) and (474,560) |
| before vs diag | **0 — byte-identical** |
| after vs after_rep | **0 — byte-identical** |
| after vs fix3 | **0 — byte-identical** |

Only two pixels in the whole page are ever unstable, and each takes one of two
values:

| pixel | left neighbour | value A | value B |
|---|---|---|---|
| (89,392) | (124,129,140) | (226,227,230) | (139,143,153) |
| (474,560) | (124,129,140) | (226,227,230) | (37,45,63) |

Both sit immediately to the RIGHT of the same 1px border colour
`(124,129,140)`, i.e. both are the first pixel past a hairline border — an
edge/antialiasing pixel that is either painted by a small alpha draw or left
at the underlying light-grey.

### The DOCUMENT pipeline is identical on every run

The `census frame=0 draws[...]` line is **byte-identical across all five
runs**: `rect_opaque=288 rect_alpha_blend=262 rect_alpha_1x1=260 rect_masked=0
rect_list=0 image_blend=262 image_blend_le16px=260 image=2 text=0 readbacks=3
readback_pixels=2052000`, with `cpu_fallback=false cpu_fallback_reason=
font_atlas_cpu_builds=0 image_scratch_fallbacks=0` everywhere. Same command
count, same kinds, same readback count, no fallback anywhere. So parse / style
/ layout / Draw IR produce the same command list every time — **the divergence
is in RASTER**, not in the document pipeline. That also retires the
dict-iteration / pointer-identity / memo-key family of suspects (F12/F13).

### Suspect shortlist (raster, narrowed by the two-pixel shape)

The unstable pixels are exactly the shape of *one small alpha draw among 260
`rect_alpha_1x1` / 260 `image_blend_le16px` draws either landing or not*:

1. **`_enqueue_framebuffer_compute` bind-chain failure**,
   `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl:660-678` —
   the source itself documents a **measured Apple M4 / MoltenVK failure where
   `vulkan_sffi_bind_pipeline` fails on the frame's SECOND dispatch through an
   already-open command buffer**, and states that when it does "the frame's
   earlier dispatches are lost either way". That is a real host/driver-timing
   dependent draw-dropping path on exactly this machine. It did not raise
   `cpu_fallback` in these runs, so if this is the mechanism it is firing on a
   narrower arm than the one that sets the flag.
2. **compute -> TRANSFER hazard is NOT covered by the post-dispatch barrier.**
   `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:5339-5358` emits,
   after every `vkCmdDispatch`, a `VkMemoryBarrier` with
   `src=SHADER_WRITE(0x40)`, `dst=SHADER_READ|SHADER_WRITE|HOST_READ(0x2060)`
   and `dstStageMask=COMPUTE_SHADER|HOST(0x4800)`. `VK_PIPELINE_STAGE_TRANSFER`
   (0x1000) and `VK_ACCESS_TRANSFER_READ` (0x800) are absent. compute->compute
   and compute->host-map are covered; any transfer-stage consumer is not.
3. **Damage-scoped mirror refresh**,
   `backend_vulkan.spl:1806-1868` (`_refresh_host_frame_damage`) — patches only
   `frame_damage_x0..x1 / y0..y1` into `host_buf` and keeps the rest of the
   previous mirror; `consume_damage_hint` (`:1751-1788`) ignores the clip and
   computes a single bounding box. A one-pixel under-coverage here leaves a
   stale mirror pixel. This route only exists when a frame is read back more
   than once — **`readbacks=3` at 900x760 vs `readbacks=1` at 300x253, which is
   exactly the size correlation the original record found.**

### Caveat the original record did not state

Every differing pair in the table above is a **different source tree**. The only
two same-tree runs (`after` / `after_rep`) were **byte-identical**, and so were
`before` / `diag`. Six runs over four trees produced three outcomes of a
two-bit state; matching values across trees is therefore not evidence of
run-to-run noise on its own. Two identical-tree Vulkan runs at 900x760 plus two
`cpu_simd` controls are in flight in `build/perf/vk_nd_2026-09-12/`; until they
land, "nondeterministic" is a hypothesis, and "the mirror/self-check path has a
real one-pixel side effect" is the live alternative.

### Both unstable pixels are GLYPH antialiasing, and the same glyph

A 17x7 luminance crop of `vk900_before.ppm` around each pixel shows white page
with thin dark stems — text, not a border. Row `y=392` and row `y=560` read
**`212 110 124 [226] 255`** and **`212 110 124 [226] 241`** at the same offsets:
the same glyph shape at two places on the page, and the unstable pixel is its
**top-row antialiasing pixel** in both.

Coverage arithmetic confirms it. With bg=(226,227,230) and dark=(37,45,63), the
stable left neighbour (124,129,140) is 0.54*dark + 0.46*bg and the alternative
value (139,143,153) is 0.46*dark + 0.54*bg — left+right sums to exactly 1.0
pixel of coverage, i.e. a ~1px stem straddling a pixel boundary. Every
`[draw-ir-font-trace]` line in these logs is `axes=wght=100`, an ultra-thin
variable weight. (`text=0` in the census is a counter gap: the per-op doc records
23 `font_composite` calls on this frame.)

This moves the font-atlas host mirror to the head of the suspect list and
demotes the framebuffer-side suspects (bind chain, TRANSFER barrier, damage
route) listed above — those cannot select a single glyph's AA byte. It also
refutes one candidate mechanism directly: the `SIMPLE_VK_FONT_SELFCHECK` block
(`backend_vulkan_font.spl:1014-1034`) writes only a local `truth` array and
`vulkan_font_mirror_note`, so it has no pixel side effect and cannot explain
`vk900_diag`. What CAN: `vk900_diag` was produced by `probe.sh`/`probe.spl`, a
**different harness** from the `run.sh`/`web_render_page_ppm.spl` used for every
other row — so that row is not comparable and should be dropped from the table.

Dropping it leaves 5 runs / 4 trees, and pixel (89,392) then partitions
*monotonically with mirror strictness*: `before` (no mirror) and `fix2`
(invalidate at function entry, the strictest) both give 226; `after` /
`after_rep` / `fix3` (mirror reused) all give 139. That is the signature of a
**deterministic stale-mirror defect**, not noise. `fix2`'s lone difference at
(474,560) is the one fact that does not fit and needs the controls below.

---

## CONFIRMED 2026-09-12: genuine run-to-run nondeterminism, ONE pixel

Two Vulkan runs of the **same tree, same binary, run sequentially**
(`build/perf/vk_nd_2026-09-12/`, `ndA` then `ndB`, HEAD of this lane,
`/Users/ormastes/simple/build/cargo-r2/release/simple`):

```
ndA vs ndB  ndiff_px = 1
  (89,392)  ndA (139,143,153)   ndB (226,227,230)
```

That settles the caveat above: it IS run-to-run nondeterministic, and the whole
effect is **one glyph antialiasing pixel out of 684,000**.

**`cpu_simd` control at the same size is deterministic**: `cpuA` and `cpuB` are
byte-identical. (Aside worth its own record: at 300x253 `cpu_simd` and the
Vulkan lane are byte-identical — 0 differing pixels — but at 900x760 they differ
in **57,807** pixels. That is a separate, much larger lane divergence and is NOT
this bug.)

Established, in order of confidence:
1. **Stage = RASTER.** The `census frame=0 draws[...]` line is byte-identical on
   every run; parse/style/layout/Draw IR emit the same command list.
2. **Blast radius = 1-2 glyph AA pixels**, at (89,392) and (474,560), each
   flipping between light `(226,227,230)` and a darker blend. Coverage
   arithmetic (above) shows a ~1px stem straddling a pixel boundary at
   `wght=100`.
3. **Size correlation** is the offscreen-group path: `image=2 readbacks=3` at
   900x760 vs `image=0 readbacks=1` at 300x253; 23 `font_composite` batches vs 5.

### Named suspect: unsynchronised host write into the device font atlas

`vulkan_sffi_copy_to_buffer(self.d_font_atlas, self.font_atlas_host_bytes, 0)`
— `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font.spl:1036` — lands in
`rt_vulkan_copy_to_buffer_fn`,
`src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:4571-4575`, which is a
**bare `dst.copy_from_slice(&bytes)` into `buffer.mapped`**: no fence wait, no
`vkFlushMappedMemoryRanges`, and no synchronisation whatsoever against font
composite dispatches already recorded/submitted that SAMPLE that same buffer.
A CPU write racing a device read of the atlas is a textbook WAR hazard, and its
observable size is exactly one sampled texel — i.e. one glyph AA pixel.

The post-dispatch barrier that does exist,
`gpu.rs:5339-5358`, does not cover this: it declares
`src=SHADER_WRITE(0x40)`, `dst=SHADER_READ|SHADER_WRITE|HOST_READ(0x2060)`,
`dstStage=COMPUTE_SHADER|HOST(0x4800)`. `VK_ACCESS_HOST_WRITE_BIT` (0x4000) and
`VK_PIPELINE_STAGE_TRANSFER` (0x1000) / `VK_ACCESS_TRANSFER_READ` (0x800) are
all absent. compute->compute and compute->host-*read* are covered; host-*write*
into a buffer the device is still reading is not.

Why this fits the size correlation: at 300x253 there are 5 font batches and one
readback (one flush), so an atlas upload rarely overlaps in-flight work; at
900x760 there are 23 batches and 3 readbacks, so far more atlas re-uploads
interleave with dispatches that have already been submitted.

Ruled out by direct source reading, so nobody re-walks them:
- the `SIMPLE_VK_FONT_SELFCHECK` block (`backend_vulkan_font.spl:1014-1034`)
  writes only locals — it has no pixel side effect;
- `_repack_atlas_dirty_cells` (`backend_vulkan_font.spl:663-703`) is proven
  byte-exact by that self-check (13 checks, 0 bad bytes);
- there is no time- or random-derived branch in `backend_vulkan*.spl` or
  `font_renderer.spl` — every `now_micros`/`rt_time_now_micros` call there is
  measurement-only, gated on a probe env var;
- document-side dict/pointer-identity memo ordering (F12/F13): the census is
  identical, so the command list is identical.

### Not fixed here, and why

The fix is in the Rust seed (`gpu.rs`), not in
`src/lib/gc_async_mut/gpu/engine2d/**`, so it is out of this diagnosis lane's
allowed files and is handed over rather than applied. The shape it needs:
either fence the atlas buffer before a host write into it, or route atlas
uploads through a staging copy with a proper `TRANSFER_WRITE -> SHADER_READ`
barrier.

### Oracle guidance (supersedes the earlier section)

The earlier advice stands, with a sharper bound: at 900x760 a whole-frame
checksum can differ **by one glyph AA pixel** between two runs of the same
tree. Use a pixel diff with a documented allowance for the two unstable
coordinates, or 300x253, never a raw checksum. The F14 corner-sprite
coalescing measurement (`web_catalog_vulkan_lane_raster_term_2026-09-12.md`,
-13.7%) should be re-run under a pixel diff: a 1-pixel-tolerance comparison,
not a checksum.

---

## CORRECTION 2026-09-12 (same session): the atlas-write suspect above is WRONG

Two claims in the section above do not survive a full read of the source and
are retracted here rather than left standing.

**Retracted: "no `vkFlushMappedMemoryRanges`".** `rt_vulkan_copy_to_buffer_fn`
DOES flush — `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:4576-4582`
builds a `VkMappedMemoryRange` over the whole allocation and calls
`flush_mapped_memory_ranges` immediately after the memcpy. The earlier claim came
from a grep window that stopped at the memcpy. Separately, the buffer memory is
allocated `HOST_VISIBLE | HOST_COHERENT` (`gpu.rs:4388`,
`flags_wanted = 0x02 | 0x04`), so a non-coherent-heap staleness story does not
apply either.

**Retracted: "a host write racing an in-flight device read".** Every submit on
this lane waits: `_flush_pending_compute`
(`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl:549-585`) calls
`vulkan_sffi_submit_and_wait_fence` and then `vulkan_sffi_wait_fence(fence, 0)`,
falling back to `wait_idle`. No engine2d backend file references
`vulkan_async_submission` at all (grep over `backend_vulkan*.spl`: zero hits).
The device is idle at every atlas upload, so there is nothing to race.

The **file:line observation still stands** and is still worth reading — the
post-dispatch barrier at `gpu.rs:5339-5358` really does omit
`VK_PIPELINE_STAGE_TRANSFER` (0x1000) and `VK_ACCESS_TRANSFER_READ` (0x800) —
but it is not established that anything on this frame consumes the framebuffer
through a transfer stage, so it is a **gap, not a diagnosis**.

### What the evidence actually constrains

`cpu_simd` is byte-identical to the Vulkan lane at 300x253 (0 differing pixels),
so it is a usable oracle. At 900x760, in a **21x21 neighbourhood** around
(89,392), `ndA` and `cpuA` differ in **exactly 1 pixel** — the glyph is rendered
identically everywhere else. The values are:

| source | (89,392) |
|---|---|
| `cpuA` / `cpuB` (deterministic) | **(124,129,140)** — the stem-core value |
| `ndA` | (139,143,153) |
| `ndB` | (226,227,230) |

So **neither Vulkan run is correct**, and the two are wrong by *different
amounts*. This is a graded one-texel value error, not a binary "the draw landed
or it didn't" — which is what a dropped dispatch or a lost blend would look
like. A graded magnitude means the *sampled coverage value* differs, so the
entropy is in what that one texel holds or in how it is blended, not in whether
a command ran.

`ndA.log` and `ndB.log` are byte-identical outside the run banner, including all
23 `[draw-ir-font-trace]` lines — a second, independent confirmation that the
document side is stable across the decisive pair. (Census identity was measured
on the five ARCHIVED runs only; those used `probe.sh`/`probe.spl`, which prints
`census`/`sum=`, whereas `ndA`/`ndB` used
`run.sh`/`examples/06_io/ui/web_render_page_ppm.spl`, which does not. The
`font_mirror_selfcheck checks=13 bad_bytes=0` result quoted earlier likewise
came from `probe.sh`, not `run.sh`.)

### Where the next session should start

1. A traced pair (`SIMPLE_VK_ORDER_TRACE=1`, two 900x760 runs) diffed for the
   first divergent line — that is the cheapest way to find the entropy source,
   and nothing in this session has located it.
2. Whether the offscreen group's content is captured via a device-side transfer
   copy. If yes, `gpu.rs:5339-5358`'s missing TRANSFER stage/access becomes the
   primary suspect and matches the size correlation (`image=2 readbacks=3` at
   900 vs `image=0 readbacks=1` at 300) better than anything else found. Read
   `_draw_image_composite_native`'s caller — do NOT edit it, F17 owns that path.
3. Whether the CPU glyph rasterizer can produce two different coverage bytes for
   the same glyph. The mirror self-check cannot see this: it compares the mirror
   against a full pack of the SAME `batch.atlas_pixels`, so shared upstream
   entropy is invisible to it.

No fix is applied. Nothing here is confirmed enough to patch, and the two
surviving candidate sites are in the Rust seed and in F17's file, both outside
this lane.

## ROOT CAUSE FOUND (2026-09-12, F19): a write race INSIDE one font dispatch

The "two surviving candidate sites are in the Rust seed" conclusion above is
superseded. The mechanism is in the packed font kernel, is visible by reading it,
and is now confirmed by a host-side census.

**The kernel.** `src/lib/common/gpu/font_atlas_composite.spl:266` — the PACKED
(batched) font composite, the one the Vulkan lane actually dispatches:

```
uint pixel = gl_GlobalInvocationID.x, glyph = gl_GlobalInvocationID.y;
...
uint d=dst[di],da=d>>24u,dwgt=da*(255u-sa)/255u,oa=sa+dwgt;
...
dst[di]=(oa<<24u)|(r<<16u)|(g<<8u)|b;
```

One invocation per **(pixel, glyph)** pair, and the blend is a plain
**non-atomic read-modify-write** on `dst[di]`. Two glyphs in the SAME dispatch
whose destination rects share a pixel are therefore two concurrent invocations
that read the same word, blend independently, and both write back: one blend is
silently dropped, and WHICH one depends on GPU scheduling. That is exactly the
signature this record documents — a graded per-texel error on thin stems where
two runs produce two DIFFERENT wrong values (139 and 226) around a CPU oracle of
124, rather than one stable wrong value.

**Confirmed, not inferred.** `SIMPLE_VK_FONT_OVERLAP=1` (added with this record)
counts ordered quad pairs with intersecting destination rects, per batch, on the
host. Measured on `css-layout.html`, same binary (`39368072 1789171430`):

| size | batches | quads | **overlapping pairs** | max in one batch |
|---|---|---|---|---|
| 900x760 | 23 | 496 | **19** | 4 |
| 300x253 | 5 | 59 | **0** | 0 |

**The census matches the symptom exactly.** 900x760 has overlapping pairs and is
the size this record found non-deterministic; 300x253 has NONE and is the size
this record and F17 both use as a byte-stable oracle. That correlation is the
strongest available evidence short of the fix: the two sizes differ in precisely
the way the mechanism predicts.

**Dispatch-to-dispatch is NOT the race.** Checked rather than assumed:
`src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:5340-5359` emits a
`vkCmdPipelineBarrier` (SHADER_WRITE -> SHADER_READ|SHADER_WRITE|HOST_READ,
COMPUTE -> COMPUTE|HOST) after EVERY `vkCmdDispatch`. Successive dispatches in
one command buffer are therefore correctly ordered. This matters twice: it
excludes the wider hypothesis, and it means the fix below is sound — sub-batches
dispatched separately are already separated by a barrier.

## The fix, and why it is cheap here

Partition each batch into sub-batches such that no two quads in ONE dispatch
overlap, dispatching them in order. Assignment must be
`bucket(q) = 1 + max(bucket(p))` over all EARLIER overlapping `p` (not first-fit):
with quads A, B, C where B overlaps A and C overlaps B but not A, first-fit puts
C in bucket 0 and dispatches it BEFORE B, inverting painter order. The `1 + max`
rule preserves it.

Cost is negligible at the measured density: 19 overlapping pairs across 23
batches, at most 4 in any one batch, so the split adds at most a couple of
dispatches per batch to the 23 already issued, each already barrier-separated.
One submit per frame is unaffected — this adds dispatches within the existing
command buffer, not submits.

## IMPLEMENTED AND PROVEN (same day)

`vulkan_font_partition_quads` assigns each quad a sub-batch index by the
`1 + max(bucket(p))` rule; `composite_font_batch` composites the sub-batches in
order when the count exceeds 1, and takes the unchanged single-dispatch path
byte for byte when it does not. Re-entry per sub-batch does NOT re-upload the
atlas: each sub-batch carries the same `atlas_generation` and owner identity, so
sub-batch 2..N takes the impl's cache-hit branch. Only sub-batch 0 carries
`dirty_rects`, so the mirror repack still happens once per real atlas change.

**The proof, measured, same binary (`39368072 1789171430`), serial runs:**

| | before the fix | after the fix |
|---|---|---|
| two 900x760 renders | checksums **8316162126305609402** and **8316164145970244972** — DIFFER | **byte-identical**, `cmp` clean over all 2,052,015 bytes, checksum `8316155370661695245` on both |
| **pixel (89,392)** | **`0x8b`=139** in one run, **`0xe2`=226** in the other | **`0x7c`=124 in BOTH** |
| 300x253 | — | `cmp` clean against F17's reference PPM |
| submits per frame | 22 | 23 — one per frame preserved (the count tracks frames, not dispatches) |

**139 and 226 are the exact two values this record measured before the cause was
known, and 124 is the CPU oracle it named.** The fix does not merely make the
page reproducible; it makes it reproduce the CPU value, which distinguishes
"the race is gone" from "the race now loses consistently".

**Cost, stated rather than buried: `font_composite` 29,459 -> 51,003 ms**, frame
191,872 -> 215,249 ms. The partition is an O(n^2) interpreted scan per batch and
every batch pays it, plus overlapping batches pay an extra params pack and
dispatch. That is a real +24 s for correctness, and it is worth it -- a
non-deterministic renderer cannot be pixel-tested at all, which is what blocked
using 900x760 as an oracle in the first place. The obvious follow-up is to make
the scan cheaper (sweep-line, or an early-out on batches below a size), not to
undo the split. The frame is still well under both F17's 259,523 ms and the
263,636 ms cpu_simd bar.
