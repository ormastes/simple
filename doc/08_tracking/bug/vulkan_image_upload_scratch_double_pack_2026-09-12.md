# The Vulkan image staging array packed every composite twice

Date: 2026-09-12. Status: **FIXED on the default byte path.**
Lane: `SIMPLE_2D_BACKEND=vulkan SIMPLE_VK_READBACK=native
SIMPLE_2D_BACKEND_STRICT=1 SIMPLE_EXECUTION_MODE=interpreter`, binary
`/Users/ormastes/simple/build/cargo-r2/release/simple`
(`stat -f '%z %m'` = `39368072 1789171430`, bracketed identical every run).
Page: `examples/06_io/ui/web_catalog/css-layout.html`, 40,960 bytes.

Split out of `vulkan_image_composite_interpreted_pack_2026-09-12.md`, which
found this while measuring something else and deliberately did not patch it:
"the right fix (shrink-to-fit, or an exact-size scratch) is a separate change
with its own oracle." This is that change.

## The defect

Three facts that are each individually reasonable and jointly cost 181 s:

1. `_prepare_image_upload` (`backend_vulkan_helpers.spl`) packs the `[u32]`
   image into `self.image_upload_scratch` and **grew that array to a high-water
   mark**, never shrinking it: `if scratch.len() < byte_count: scratch = [0u8;
   byte_count]`. Reusing a buffer instead of reallocating per composite is the
   textbook move.
2. `vulkan_sffi_copy_to_buffer_prefix` (`sffi_vulkan.spl:1279`) uploads only the
   initialized prefix — but on the **interpreter array ABI** the only available
   extern derives the length from the array itself, so it can admit a prefix
   only when `byte_count == data.len()`, and fails closed otherwise. Failing
   closed is correct; a partial upload would paint garbage.
3. The caller treats a declined prefix as "use the exact-size legacy path",
   which calls `_pixels_to_bytes(pixels, pixel_count)` — **a second complete
   interpreted walk of the same image**.

So after the first large composite, every SMALLER one had
`byte_count < scratch.len()`, was refused, and packed the whole image again.
The reuse optimisation *caused* an extra full pack on all but the first two
composites. Nothing was wrong on the wire: both packs produce identical bytes,
which is exactly why no pixel, checksum or PPM comparison could ever have
caught it. Only a counter can.

## Measured, 900x760, flag OFF (the default byte path)

| bucket | n | before ms | after ms |
|---|---|---|---|
| **frame** | | **830,186** | **571,045 (-31.2%)** |
| image_composite | 264 | 573,780 | **343,784 (-40.1%)** |
| image_pack_u32_to_u8 | 264 | 391,259 | 342,969 |
| **image_exact_size_byte_fallback** | **262** | **180,995** | **0 — bucket never fires** |
| rect / image_blend | 550/262 | 288,153/287,818 | 173,099/172,817 |

The "before" column is the flag-OFF run recorded in the parent bug on the same
binary; the "after" is a fresh flag-OFF run on the same binary with only this
change applied. **259 seconds off the default byte-path frame**, which is the
lane every binary predating `rt_vulkan_copy_to_buffer_u32` is stuck on.

The one remaining pack (`image_pack_u32_to_u8`, 342,969 ms) is the *first*,
necessary walk — the one the typed `[u32]` lane removes. This change removes the
second, redundant one. `rect` and `image_blend` are outer buckets that WRAP the
composite, so their fall is the same saving counted once more, not a second fix.

Frame checksum `8316155854136152477` vs the parent run's
`8316162126305609402`: that is the nondeterminism F16 records for this page at
this size (`web_catalog_900x760_frame_checksum_nondeterministic_2026-09-12.md`),
not evidence about this change. The deterministic oracle is 300x253, where the
checksum is byte-identical to the parent run (`-6077680819631676143`).

## The fix

One character of logic and a comment that explains why it is not a style
preference: size the scratch to **exactly** `byte_count`
(`scratch.len() != byte_count` rather than `<`). The prefix is then always the
whole array, the interpreter-ABI admission test holds for every size, and
`_pixels_to_bytes` becomes dead for every admitted composite.

What this trades away, stated rather than hidden: a size CHANGE now costs one
runtime-side allocation. That is strictly cheaper than the second interpreted
walk it replaces — a `[0u8; n]` allocation is one runtime call, the walk is
`4 * pixel_count` interpreter steps — and a repeated size still reuses the same
array, which the spec pins directly (three same-size uploads, one resize).

The alternative design, per-size scratch buckets, was not built: it keeps every
size alive for the process lifetime (the largest source here is 12.87M pixels,
51 MB) to avoid an allocation that is already cheaper than the thing it
replaces.

## Why this matters after the typed lane landed

`SIMPLE_VK_IMAGE_UPLOAD=u32` bypasses BOTH packs, so on that lane this defect is
unobservable. But the typed lane is opt-in and must stay opt-in — calling
`rt_vulkan_copy_to_buffer_u32` on a binary that predates the extern aborts the
process from inside the interpreter's unknown-extern path, before any in-tree
guard can decline (`typed_vulkan_upload_no_fallback_on_old_binary_2026-09-11.md`).
The byte path is therefore what every default process runs, and what every older
binary runs with no choice at all. Fixing it benefits the lane the typed flag
cannot reach.

## Guard against regression

`test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_image_exact_scratch_spec.spl`
— device-requiring (fails, never skips), run with `SIMPLE_VK_IMAGE_UPLOAD`
UNSET. Absolute oracles, not thresholds:

- one composite reads `packs=1 byte_fallbacks=0 scratch_resizes=1`;
- **a 4x4 image after a 40x40 one reads `packs=2 byte_fallbacks=0
  scratch_resizes=2`** — the defect, in its minimal shape;
- the small image's 16 pixels are each checked against a per-pixel-distinct
  oracle, and so are the large image's 1,600 when the order is reversed, so a
  change that stopped uploading could not satisfy the counters;
- three same-size uploads read `scratch_resizes=1`, pinning that reuse survived.

The counters are process-wide module globals reached through the engine facade
(`vulkan_image_pack_evidence`), because the facade does not expose the backend
struct; each example resets them first.

## Sabotage: the oracle discriminates

Restoring the high-water test (`!=` back to `<`) in `_prepare_image_upload`:

```
x packs a SMALLER image after a larger one exactly once, not twice
  expected "packs=2 byte_fallbacks=1 scratch_resizes=1" to equal
           "packs=2 byte_fallbacks=0 scratch_resizes=2"
```

Every pixel expectation in the file stays GREEN under that sabotage — which is
the point, and the reason the counter had to be added at all.

## Not fixed here

The `vulkan_sffi_copy_to_buffer_prefix` interpreter-ABI restriction itself. The
right fix there is a bounded-length extern on the interpreter array ABI
(`rt_vulkan_copy_to_buffer_array` already exists for the native lane), which is a
seed change, not a pure-Simple one. Until that lands, the exact-size scratch is
what makes the existing facade usable for every size rather than only the
largest one seen so far.
