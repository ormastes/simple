# Vulkan font atlas: the last host pixel loop on the GPU boundary (F36)

RESOLVED 2026-09-12 behind `SIMPLE_VK_FONT_UPLOAD=u32` (default OFF).

## Symptom

After the readback and submit lanes went green, the GPU-boundary audit gate
(`scripts/check/check-web-vulkan-gpu-boundary-audit.shs`, overview.html
900x760, interpreter, `SIMPLE_2D_BACKEND=vulkan`) reported exactly ONE
remaining violation:

```
FAIL — 2 frame(s) audited, violated: host_pixel_iterations=15 (>0): font_atlas_pack_u32_to_u8
```

`host_pixel_iterations` counts LOOP INVOCATIONS in the
`font_atlas_pack_u32_to_u8` timing bucket. Each invocation of
`_vulkan_font_pixels_to_bytes` walks the fixed 1024x1024 atlas: 1,048,576
interpreted iterations, four host array stores each.

## Root cause

Not the font lane's algorithm — F16/F24/F32 already reduced the pack to dirty
cells, per-owner mirrors and owner-keyed device slots. The pack exists only
because of the SFFI signature: `vulkan_sffi_copy_to_buffer` /
`rt_vulkan_copy_to_buffer` marshal through `strict_owned_bytes`, which
truncates every array element to one byte. `batch.atlas_pixels` is already
`[u32]`, so a word payload must be exploded into four `[u8]` stores per pixel
before it can be handed over. The host mirror, and the incremental repack that
keeps it cheap, are downstream consequences of that byte payload — not of any
device requirement.

`vulkan_sffi_copy_to_buffer_u32` (PR #534) takes the words as words and widens
them in Rust over the whole array at once. With it, the font lane hands over
`batch.atlas_pixels` untouched: no pack, no mirror write, no repack.

## Fix

`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font.spl` +
`backend_vulkan_helpers.spl`:

- New opt-in `SIMPLE_VK_FONT_UPLOAD=u32` (`vulkan_font_upload_u32_requested()`),
  default OFF — same shape and the same reason as the rect and image flags:
  calling `rt_vulkan_copy_to_buffer_u32` on a binary built before the extern
  existed aborts the whole process from the interpreter's unknown-extern path,
  before any guard can decline
  (`typed_vulkan_upload_no_fallback_on_old_binary_2026-09-11.md`).
- When set, the atlas upload branch calls
  `vulkan_sffi_copy_to_buffer_u32(self.d_font_atlas, batch.atlas_pixels, 0)`
  and skips the repack, the full pack, the mirror self-check compare and
  `vulkan_font_pack_note` — a pack that did not run must not be counted, or
  `atlas_full_repacks=15` alongside `host_pixel_iterations=0` would be
  self-contradicting evidence.
- The byte path is untouched and remains the default AND the fallback: a typed
  upload that returns false falls through to it in the same run
  (`typed-declined`), so a runtime refusal degrades rather than drops pixels.
- F24/F32 continuity preserved: in the typed lane the host byte mirror is never
  built, so the two predicates that read its BYTES are made typed-aware — the
  `len == atlas_bytes` input to `vulkan_font_mirror_continuity`, and
  `_font_mirror_activate`'s park condition. Both then carry the identity /
  generation / sequence triple alone, which is exactly what the continuity
  verdict and the slot plan actually read. Without this, no owner could ever be
  parked and every owner switch would degrade to a full write.
- No decision note is emitted on the typed path on purpose:
  `vulkan_font_decision_note` shares a fixed 4000-char budget with the slot and
  continuity notes, and one extra line per composite truncates the sequence a
  mirror investigation reads.
- `scripts/check/check-web-vulkan-gpu-boundary-audit.shs` arms
  `SIMPLE_VK_FONT_UPLOAD="$UPLOAD_MODE"` next to the rect and image flags, so
  `--upload-mode bytes` still exercises the fallback end to end.

## Evidence (binary `build/cargo-r2/release/simple`, 39528776 1789199850, unchanged across every run)

overview.html 900x760, 2 frames:

| key | bytes (before) | u32 (after) |
|---|---|---|
| verdict | FAIL host_pixel_iterations=23 | **PASS** |
| `host_pixel_iterations` | 23 (font 15, image 8) | **0** (`none`) |
| `atlas_full_repacks` | 4 | 0 |
| `upload_ms` | 146 | **45** |
| `submits_per_frame` | 1 | 1 |
| `readbacks_per_frame` | 1 | 1 |
| `dispatches_per_frame` | 107 | 107 |
| `uploads_per_frame` | 23 | 23 |
| `fence_waits` | 1 | 1 |
| `frame_digest` | `a15c50cd` | **`a15c50cd`** |

```
PASS — 2 frame(s) audited, host_pixel_iterations=0, readbacks_per_frame<=1, submits_per_frame<=1
```

css-layout.html 900x760, 2 frames: `host_pixel_iterations` 47 (font 20, image
27) -> **0**, `upload_ms` 184 -> 58, `frame_digest` `811c9dc5` both, submits 3
both. That page still FAILs on `submits_per_frame=3 (>1)` — a pre-existing
violation of a different lane, untouched here and not this bug.

Equality of every op count and of `frame_digest` across the two lanes is the
byte-fallback equivalence proof: the typed lane changes only HOW the bytes
cross the boundary.

**Sabotage (temporary edit, reverted):** byte-swapping each word immediately
before `vulkan_sffi_copy_to_buffer_u32` kept the gate PASSing on counts
(`host_pixel_iterations=0`) and moved `frame_digest` to `acadc75d`. Restoring
the passthrough returned `a15c50cd`. The typed upload therefore genuinely
carries the glyph coverage, and the digest — not the counts — is what witnesses
it.

**Self-check:** `SIMPLE_VK_FONT_SELFCHECK=1` runs clean in both lanes (no
`atlas-slot-owner-mismatch`, no mirror mismatch), `frame_digest=a15c50cd` in
both. The typed lane records no mirror checks because it builds no mirror;
its pixel evidence is the digest above.

## Specs kept green (seed `build/cargo-r2/release/simple run`)

- `backend_vulkan_font_atlas_slot_plan_spec` 12/12 (F32)
- `vulkan_font_atlas_incremental_repack_spec` 30/30 (F24)
- `backend_vulkan_font_quad_partition_spec` 7/7 (F19)
- `backend_vulkan_drawing_spec` 44/44
- NEW `backend_vulkan_font_typed_upload_spec` 4/4 (8 oracles): the flag is
  opt-in by default, and the mode/reason evidence separates
  `typed-not-requested` from `typed-declined`.

Not runnable on this host, for reasons independent of this change and
unchanged by it: `backend_vulkan_blend_cpu_parity_spec`,
`backend_vulkan_device_glass_blur_spec` and `backend_vulkan_font_spec` all
fail to resolve their imports under `simple run` (`E1034`, `gpu` / `spec`
module path), and the `simple test` runner exceeds its 930s outer bound on
this box. Stated rather than claimed green.

## Residual

`uploads_per_frame=23` on overview (15 of them font atlas) means the typed lane
now memcpys ~60 MB of atlas per frame instead of packing it. That is a large
net win (`upload_ms` 146 -> 45) but the upload COUNT itself is a separate lane's
bug: the atlas is re-uploaded per run rather than once per owner per frame. Not
fixed here.

## Pre-push divergence step-over (recorded per `.claude/rules/vcs.md`)

`check-test-tree-divergence` is RED at `origin/main` independently of this
change: `FAIL — 3943 diverged vs 965 baselined (3081 new, 103
fixed-but-still-baselined); 26 mirror-only (25 unallowlisted)`. The scoped
delta is clean:

```
check-test-tree-divergence-delta: PASS — 3209 pre-existing offender(s), 0 introduced by this range
```

Pre-existing offender list as captured by the helper:
`$TMPDIR/test_tree_divergence_preexisting.txt` (3209 entries, all pre-existing
at `origin/main` @ `97afb84fb79`). This range adds a single NEW spec file
(`test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_typed_upload_spec.spl`)
with no mirror twin in `test/unit/`, and introduces no divergence.
