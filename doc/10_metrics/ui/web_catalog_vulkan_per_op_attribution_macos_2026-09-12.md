# Vulkan lane per-op attribution, css-layout.html (macOS M4, 2026-09-12)

Binary bracketed identical every run: `build/cargo-r2/release/simple`,
`stat -f '%z %m'` = `39368072 1789171430`. `SIMPLE_2D_BACKEND=vulkan
SIMPLE_VK_READBACK=native SIMPLE_2D_BACKEND_STRICT=1 SIMPLE_VK_TIMING=1
SIMPLE_EXECUTION_MODE=interpreter`, one at a time (serial: concurrent runs
contend for the same GPU). Page `css-layout.html`; logs gitignored.

## 300x253 — where the frame goes (ms)
| bucket | n | before | after |
|---|---|---|---|
| **font_atlas_pack_u32_to_u8** | 5 | **19,012** | **7,433** |
| font_atlas_payload_sha256 | 5 | 8,234 | 8,308 |
| font_composite (total) | 5 | 27,348 | 15,669 |
| **frame** | | **47,646** | **35,389 (-25.7%)** |

The atlas is a fixed **1024x1024 (4 MB)** whatever the glyph count, so each
pack/digest is ~1M interpreted iterations, and it was genuinely dirty every time
(generations `2 3 4 6 7` ascend) — the waste was rebuilding 4 MB for a few new
cells, not a falsely-missing cache. Fix: mirror repacked only over
`batch.dirty_rects` (`pack_full=2 pack_incremental=3`); PPM byte-identical.

## 900x760 — a DIFFERENT dominant term

| bucket | n | before | after |
|---|---|---|---|
| frame | | 863,307 | **789,177 (-8.6%)** |
| font_composite | 23 | 113,668 | **61,463 (-45.9%)** |
| **image_composite** | 264 | 568,149 | **544,646** |
| rect / image_blend | 550/262 | 286,068 | 270,139 |

`image_composite` is **69% of the frame** and its SFFI upload is 237 ms across
all 264 calls, so the cost is interpreted host work.

Those probes were built and run (2026-09-12, same binary). **The sub-step is no
longer unmeasured, and the fallback hypothesis is excluded:** `reasons: ok=264`
— every composite took the device path, none fell to `emu_draw_image_*`. The
cost is host packing, and it is paid **twice** per composite: 391,259 ms in
`image_pack_u32_to_u8` plus 180,995 ms in `image_exact_size_byte_fallback`,
which fires 262 of 264 times because `vulkan_sffi_copy_to_buffer_prefix`
(`sffi_vulkan.spl:1279`) admits a prefix on the interpreter ABI only when
`byte_count == data.len()`, and the scratch is never shrunk. Device work is
1.3 s total (alloc 315, dispatch 94, upload 907). `max_px=12,874,224` — the
largest source is 18.8x the surface.

Routing the upload through `vulkan_sffi_copy_to_buffer_u32`
(`SIMPLE_VK_IMAGE_UPLOAD=u32`, opt-in) skips both packs, since `pixels` is
already `[u32]`:

| bucket | n | before | after |
|---|---|---|---|
| **frame 900x760** | | **830,186** | **259,523 (-68.7%)** |
| image_composite | 264 | 573,780 | **940** |
| both pack buckets | 264/262 | 572,254 | **0 (never fire)** |
| font_composite | 23 | 68,745 | 70,708 |

**Target MET: 259,523 ms vs the 263,636 ms cpu_simd bar.** PPM **byte-identical**
at BOTH sizes (`cmp` clean; 300x253 is the deterministic oracle, the 900x760
pair also matched but F16 means a future difference there is noise, not
evidence). `upload_reason=typed-requested` confirms the typed lane ran — the two
lanes write identical bytes, so no pixel can witness it. 300x253 is unchanged
(30,861 -> 33,403 ms, noise): all 76 composites there are 1x1, nothing to pack.
Origin: `simple_web_html_engine2d_presenter.spl:597` uploads a host-rasterized
full layout surface and reads it straight back (NOT an eliminable identity
blit) — but that only explains the 684k-px class; the 12.87M-px source is a
scaled/synthesized draw at `draw_ir_adv.spl:2263/2289/2291`, not pinned further.
`font_composite` is now the dominant term. No upload cache: no O(1) array
identity or producer generation exists, and an interpreted digest is the same
O(n) class as the pack (`font_atlas_payload_sha256` = 8.3 s). Detail:
`doc/08_tracking/bug/vulkan_image_composite_interpreted_pack_2026-09-12.md`.

## Correctness oracle
`SIMPLE_VK_FONT_SELFCHECK=1` compares the mirror to a full pack after every
incremental repack: `checks=13 bad_calls=0 bad_bytes=0` at 900x760. **Do not
rely on the 900x760 frame checksum** — F16 records the page as
non-deterministic there; use 300x253 for a byte oracle.

**Target: MET at 900x760, still missed at 300x253.** The typed `[u32]` upload
was the predicted fix and it landed; caching, as predicted, was not needed and
is not implemented. At 300x253 the backend is font-bound (~16.5 s vs the ~5.4 s
parity budget), and the remaining O(atlas) walks — digest 8.3 s, 2 full repacks
7.4 s — are unchanged by this work.

Pooled-slot counters (`dispatches_frame=1 submits=0` vs 111 drawn rects) read a
backend that did not draw — use the module-global `vulkan_timing_*` /
`vulkan_font_pack_*`.

## F19 (2026-09-12): the double pack, the atlas digest, and the font race

Same binary throughout, bracketed identical (`stat -f '%z %m'` =
`39368072 1789171430`), same page, serial runs.

### 1. Default BYTE path — the double pack is gone (helps every old binary)

`_prepare_image_upload` sized `image_upload_scratch` to a high-water mark while
`vulkan_sffi_copy_to_buffer_prefix` admits a prefix only when
`byte_count == data.len()`, so 262 of 264 composites were refused and packed a
SECOND time. Exact-size staging (900x760, `SIMPLE_VK_IMAGE_UPLOAD` unset):

| bucket | n | before | after |
|---|---|---|---|
| **frame** | | **830,186** | **571,045 (-31.2%)** |
| image_composite | 264 | 573,780 | **343,784 (-40.1%)** |
| **image_exact_size_byte_fallback** | 262 | **180,995** | **0 (never fires)** |
| rect / image_blend | 550/262 | 288,153/287,818 | 173,099/172,817 |

This is the lane the typed flag cannot reach, and 259 s came off it.
Detail: `doc/08_tracking/bug/vulkan_image_upload_scratch_double_pack_2026-09-12.md`.

### 2. `font_composite` attributed, and its top term removed

The F17 table above named `font_composite` (70,708 ms) as dominant. It is TWO
O(atlas) interpreted walks and nothing else — the 1024x1024 atlas is 4 MB
whatever the glyph count:

| bucket | n | before | after |
|---|---|---|---|
| **font_composite** | 23 | **70,708** | **29,419 (-58.4%)** |
| **font_atlas_payload_sha256** | 21 | **37,650 (53%)** | **137 (-99.6%)** |
| font_atlas_pack_u32_to_u8 | 21 | 32,672 (46%) | 28,932 |
| font_atlas_sffi_upload | 21 | 211 | 175 |
| font_packed_params | 23 | 52 | — |
| font_quad_validate | 23 | 16 | — |

**Everything the brief anticipated as a cost is 280 ms, 0.4%** — per-run params
packing (52 ms), glyph quad packing, the descriptor/params pool and per-run
submit. A `SIMPLE_VK_FONT_UPLOAD=u32` typed lane was therefore scoped and
**deliberately not built**: it would target 52 ms. That is a finding, not an
omission.

The digest was EVIDENCE — every consumer asserts its shape (`.len() == 64`,
`lower_hex_sha256_valid`); the re-upload decision is made by
`(atlas_generation, owner_identity)`, and the generation bumps only when
`dirty.len() > 0` (`font_renderer.spl:2293-2298`), i.e. only on a real glyph
insert. Folding that pair through the same `sha256_u8_hex` envelope keeps every
assertion holding at O(1). `SIMPLE_VK_FONT_DIGEST=payload` restores the walk.

At 300x253: `font_atlas_payload_sha256` **8,234 -> 32 ms**, frame
**33,403 -> 20,678 ms**, and the frame checksum is **byte-identical**
(`-6077680819631676143`) — the deterministic oracle, so this is pixel-neutrality
measured rather than assumed.

### 3. The 900x760 nondeterminism has a root cause

`SIMPLE_VK_FONT_OVERLAP=1` counts intersecting destination-rect quad pairs per
batch: **900x760 = 19 pairs (max 4 in one batch); 300x253 = 0**. The packed font
kernel (`font_atlas_composite.spl:266`) runs one invocation per (pixel, glyph)
and blends with a NON-ATOMIC read-modify-write on `dst[di]`, so overlapping
quads in one dispatch race. The census correlates exactly with which size is
non-deterministic. Dispatch-to-dispatch is excluded: a `vkCmdPipelineBarrier`
follows every `vkCmdDispatch` (`interpreter_extern/gpu.rs:5340-5359`).
Recorded in `web_catalog_900x760_frame_checksum_nondeterministic_2026-09-12.md`.

### Target: MISSED, and the arithmetic says why

The brief set ≤ 150,000 ms at 900x760. Measured clean (no census
instrument): **191,872 ms**, from F17's 259,523 — a 26% reduction. With the
font race fix also applied (below) it is **215,249 ms**, because removing the
nondeterminism costs ~24 s. The remaining `font_composite` is 28,932 ms of full atlas repacks
driven by `identity_changed=8` — the page alternates between two font identities
and the backend keeps ONE host mirror, so each flip repacks 4 MB. A per-owner
mirror would remove it, leaving a floor near **166,000 ms**.

That floor is not Vulkan work. The document pipeline is 29,451 ms (style cascade
alone 25,229) and the rest is the host rasterization of the full-layout surface
that `simple_web_html_engine2d_presenter.spl:597` then uploads and reads straight
back — the GPU is a pass-through. Reaching 150 s means not rasterizing on the
host, which is a different and much larger change. The cpu_simd bar on this page
is 263,636 ms; the Vulkan lane is now well under it.

### 4. The font race fix, and what it costs

The partition described in §3 is implemented. Two 900x760 renders are now
**byte-identical** (`cmp` clean, checksum `8316155370661695245`) where before
they differed, and **pixel (89,392) reads 124 — the CPU oracle value — in both**,
where before it read 139 in one run and 226 in another. 300x253 is `cmp` clean
against F17's reference PPM. Submits per frame: **22, unchanged**.

| | F17 | + image/digest fixes | + race fix |
|---|---|---|---|
| **frame 900x760** | 259,523 | **191,872** | **196,121 / 194,530** |
| font_composite | 70,708 | 29,459 | 29,529 |
| pack_full | 8 | 8 | 8 |
| 900x760 reproducible | no | no | **yes** |

**The race fix costs ~4 s** — the split adds a few dispatches to a command
buffer whose dispatches are already barrier-separated, and the overlap scan is
cheap at these glyph counts.

An intermediate version cost 24 s and the counters said why: the sub-batch
helper let `atlas_owner_generation` and `render_config_identity` default, so
every sub-batch read as a new atlas owner and forced a full repack (`pack_full`
8 -> 14, `font_atlas_pack_u32_to_u8` 28,949 -> 50,487 ms). Carrying every field
restored it. Recorded because the failure was invisible except in `pack_full`:
no error, no pixel change, just triple the cost.

### Final honest position on the target

**≤150,000 ms: MISSED.** 196,121 ms with everything applied, from F17's
259,523 — a 24% reduction, and reproducible for the first time. The one named
remaining Vulkan term is 29,021 ms of full atlas repacks
(`identity_changed=8`: two alternating font identities share ONE host mirror; a
per-owner mirror removes it), which would leave ~167,000 ms. That floor is host
rasterization plus the 29,451 ms document pipeline, not GPU work — the presenter
rasterizes the page on the CPU and uses the GPU as a pass-through. The cpu_simd
bar on this page is 263,636 ms.

## Appended 2026-09-12 (F-follow-up): two hypotheses measured, both refuted

Same binary `/Users/ormastes/simple/build/cargo-r2/release/simple`, same page,
`SIMPLE_2D_BACKEND=vulkan SIMPLE_VK_READBACK=native SIMPLE_VK_IMAGE_UPLOAD=u32
SIMPLE_2D_BACKEND_STRICT=1 SIMPLE_EXECUTION_MODE=interpreter`, serial.

### 1. The Draw IR route sampler never runs on this lane

New level-gated stage counters (`SIMPLE_WEB_ROUTE_STAGES=1`, read-only) on
`simple_web_layout_engine2d_fast.spl`, at **both** sizes:

```
route_stages oracle_raster_ms=0 oracle_n=0 present_upload_ms=0 present_n=0 \
  gpu_route_ms=0 gpu_n=0 consults=0 canonical_submissions=0 cached_reuses=0
```

`_web_draw_ir_choose_route` is never entered: every call site is behind
`web_gpu_paint_enabled()`, which needs `SIMPLE_WEB_GPU_PAINT=1`, never set on
this lane. There is no per-document software-oracle A/B pass to remove, and no
probe-authorization mechanism was built. The host-raster floor comes instead
through `simple_web_html_engine2d_presenter.spl:~597` (not owned here). Detail:
`doc/08_tracking/bug/web_vulkan_lane_per_document_software_sampling_2026-09-12.md`.

### 2. Per-owner atlas mirrors change nothing on this page

Controlled by `SIMPLE_VK_FONT_PER_OWNER_MIRROR` (same binary, same tree):

| size | per-owner | pack_full | pack_incremental | identity_changed | PPM |
|---|---|---|---|---|---|
| 300x253 | off | 2 | 3 | 2 | — |
| 300x253 | on | 2 | 3 | 2 | `cmp` clean vs off |
| 900x760 | off | 8 | 13 | 8 | — |
| 900x760 | on | 8 | 13 | 8 | `cmp` clean vs off |

Cause: `atlas_generation` is ONE global counter shared by all owners, so an
interleaved page always violates the `+1` continuity rule the incremental repack
requires — generations `[2 4 5 6 7 8 9 9 10 11 11 12 12 13 15 17]`. The fix needs
a per-owner sequence field on `FontRenderBatch` (`font_renderer.spl`, not owned
here). Detail:
`doc/08_tracking/bug/vulkan_font_atlas_shared_mirror_repacks_2026-09-12.md`.

`test/02_integration/gpu/vulkan_font_atlas_incremental_repack_spec.spl`:
**14 examples, 0 failures** with the per-owner cache in the tree.

### Wall clock is not usable as evidence at this size right now

Three 900x760 runs of essentially the same work: **226 s, 336 s, 584 s** under
concurrent agent load on this host. The ≤100 s target is **MISSED**, and with the
two candidate terms refuted the remaining floor is the presenter's host raster,
which this lane does not own. Reported honestly rather than fitted.

### 3. Stage table at 900x760 — 82% of the cold render is outside the Vulkan backend

Control run (`SIMPLE_VK_FONT_PER_OWNER_MIRROR=0`, `SIMPLE_VK_TIMING=1`), 336 s wall:

| bucket | n | total ms |
|---|---|---|
| font_composite | 23 | 54,103 |
| — font_atlas_pack_u32_to_u8 | 21 | 53,221 |
| — font_atlas_sffi_upload | 21 | 326 |
| — font_atlas_payload_sha256 | 21 | 261 |
| rect | 550 | 1,285 |
| image_composite | 264 | 1,056 |
| image_blend | 262 | 858 |
| readback | 2 | 1,540 |
| **Σ backend** | | **~59,000** |
| **wall − Σ** | | **~277,000 (82%)** |

The font atlas pack is still the dominant backend term (53 s, 8 full packs), and
everything else on the device is noise. The remaining 277 s is host work in
parse/style/layout/Draw IR and the present path — **bounded here, not located**,
and not instrumented by this lane. An earlier claim in the sampling record that
pinned it to `simple_web_html_engine2d_presenter.spl:~597` was retracted: that
function's call from `_web_draw_ir_upload_route` is on the dead sampler path.

## F22 — per-owner atlas sequence + producer-side park (2026-09-12)

Two binary identities were in play and both are recorded, because the shared
`build/cargo-r2/release/simple` was **replaced by another agent mid-session**:
`39368072 1789171430` (all runs below) and `39178424 1789197971` (the
replacement, which is a partial build: it fails the lane outright with
`semantic: unknown extern function: rt_vulkan_copy_to_buffer_u32` and
`rt_vulkan_readback_u32_array`, symbols this tree DOES register in
`compiler/src/interpreter_extern/gpu.rs` — so the regression is in that build,
not in this change). A control run with the fix disabled fails identically on
it, which is how the swap was distinguished from a defect in this lane.

Env: `SIMPLE_2D_BACKEND=vulkan SIMPLE_VK_READBACK=native
SIMPLE_VK_IMAGE_UPLOAD=u32 SIMPLE_2D_BACKEND_STRICT=1 SIMPLE_VK_TIMING=1
SIMPLE_EXECUTION_MODE=interpreter SIMPLE_VK_FONT_SELFCHECK=1
SIMPLE_TIMEOUT_SECONDS=0`, page `css-layout.html`, one run at a time. The
before/after control is `SIMPLE_FONT_ATLAS_PARK=0`, so both sides come from one
binary and one tree.

| size | park | pack_full | pack_incremental | identity_changed | font_atlas_pack (ms, 21/5 calls) | selfcheck |
|---|---|---|---|---|---|---|
| 300x253 | off (control) | 2 | 3 | 2 | 101,367 | `bad_calls=0 bad_bytes=0` |
| 300x253 | **on** | **2** | **3** | 2 | 107,084 | `bad_calls=0 bad_bytes=0` |
| 900x760 | off (control) | 8 | 13 | 8 | 200,246 | `bad_calls=0 bad_bytes=0` |
| 900x760 | on | *not measured — binary swapped* | | | | |

PPM `cmp` at 300x253 is **byte-identical** between control and fix.

**Honest gaps.** (1) The 900x760 after-run is NOT measured: every attempt after
the binary swap dies in the extern registry before reaching the frame, for the
control as well. The 900x760 control above reproduces the defect exactly
(`pack_full=8 = identity_changed=8`), so the before side is pinned; the after
side is owed. (2) 300x253 already sat at `pack_full == 2 == distinct owners`
before this change, so it cannot discriminate — it is reported as the
pixel-safety and no-regression control it is, not as evidence of the fix.
(3) The ms column is ~14x the pre-F21 figures in the tables above for the same
work; the host is shared with other agents and wall clock here is
**informational only**, exactly as F21 recorded. The counters are the evidence.

### F22 900x760, measured on a privately-built binary

The shared binary's replacement could not run this lane, so the seed was rebuilt
from this tree into a private `CARGO_TARGET_DIR`: **`37568056 1789199216`**.
Same env as above.

| size | park | pack_full | pack_incremental | identity_changed | continuity 0/1/2 | selfcheck | font_atlas_pack ms |
|---|---|---|---|---|---|---|---|
| 300x253 | on | 2 | 3 | 2 | — | `bad_calls=0 bad_bytes=0` | — |
| 900x760 | on | **8** | 13 | 8 | **16 / 26 / 0** | `bad_calls=0 bad_bytes=0` | 197,481 (21 calls) |

`pack_full` is unchanged and that is the finding, not a failure of the change.
Of the 16 full decisions, the 8 that correspond to `identity_changed` carry
`owner_match=false len_match=false` — **no parked mirror existed for the
incoming owner**. Every other decision is `owner_match=true len_match=true` with
exactly contiguous sequences (`seq=7 host_seq=6` … `15←14`), i.e. the per-owner
sequence works wherever an owner recurs. On this page no owner ever recurs: the
shaped-run identity is the combined face SET, so each joining face mints an
identity never seen before and a full repack is correct.

**`pack_full == 2` was therefore an unreachable target for this page** — it has
8 distinct owners, not 2 alternating. The lever is to stabilise the owner
identity (key on the atlas instance, not the face-set string); see the bug
record.

Newly established here and not before: the incremental mirror has now been
compared against a full pack **26 times on the live page** with
`bad_bytes=0` — the first real soundness evidence for the park + sequence
pairing, which F21 could not obtain because `can_increment` never fired.

#### Same-binary 900x760 A/B (both runs on `37568056 1789199216`)

| park | pack_full | pack_incremental | selfcheck |
|---|---|---|---|
| off (control, `SIMPLE_FONT_ATLAS_PARK=0`) | 8 | 13 | `bad_calls=0 bad_bytes=0` |
| on | 8 | 13 | `bad_calls=0 bad_bytes=0` |

PPM `cmp` **byte-identical** between the two. The change is pixel-safe and, on
this page, inert — the producer wipes the atlas 6-8 times per frame (the +3
sequence signature), which no continuity rule can recover. The earlier
900x760 control on the replaced shared binary (`39368072`) agreed
(`pack_full=8 pack_incremental=13`) but is NOT the control for these runs and
is not used as one.

Decision notes are exactly 2x the pack counters (42 vs 21, 16 vs 8, 26 vs 13):
the sub-batch partition splits each composite into two decisions.

#### F22b — park key captured at activation (the fix for the key mismatch)

The park filed slots under a key re-derived at park time from
`atlas_font_identity` / `atlas_face_generation`, which the shaped-run `-2`
branch and the overflow resets rewrite between switches, so a slot was stored
under a name the next lookup never asked for. `atlas_active_park_key` now
captures the key when the owner BECOMES active. One verification run, park ON,
same private binary `37568056 1789199216`, same env:

| | park trace | pack_full | pack_incremental | continuity 0/1/2 | selfcheck |
|---|---|---|---|---|---|
| before (key re-derived) | 5 reset, **0 restore** | 8 | 13 | 16 / 26 / 0 | `bad_calls=0 bad_bytes=0` |
| after (key captured) | 2 reset, **3 restore** | **5** | **15** | 10 / 28 / **2** | `bad_calls=0 bad_bytes=0` |

PPM `cmp` **byte-identical** to the park-OFF control. `pack_full` 8 -> 5 is
three 1,048,576-pixel repacks removed, one per restore. `continuity=2`
(ALREADY_TRUTH) fires for the first time on a live page (2x), so that outcome is
no longer spec-only. `pack_full == 2` is still not reached: 2 resets remain (the
two cold first-sightings) plus the sub-batch partition's share of the 10 full
decisions.

## Atlas upload-once + degenerate-dispatch fix (2026-09-12, same binary 39528776/1789199850)

`SIMPLE_EXECUTION_MODE=interpreter SIMPLE_2D_BACKEND=vulkan SIMPLE_VK_READBACK=native`
`SIMPLE_VK_{IMAGE,RECT,FONT}_UPLOAD=u32`, 900x760, 2 frames, via
`scripts/check/check-web-vulkan-gpu-boundary-audit.shs`.

| page | uploads/frame | upload_ms | submits/frame | fence_waits | frame_digest | verdict |
|---|---|---|---|---|---|---|
| overview before | 23 | 43 | 1 | 1 | a15c50cd | PASS |
| overview after | 13 | 19 | 1 | 1 | a15c50cd | PASS |
| css-layout before | 47 | 57 | 3 | 3 | 743c2081 | FAIL |
| css-layout after | 25 | 32 | 1 | 1 | 743c2081 | PASS |

Digests unchanged on both pages. Detail and mechanism:
`doc/08_tracking/bug/vulkan_font_atlas_reupload_per_run_and_css_layout_submits_2026-09-12.md`.
