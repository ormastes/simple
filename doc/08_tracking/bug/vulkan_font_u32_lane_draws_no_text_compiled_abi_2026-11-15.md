# Vulkan font u32 upload lane draws no text under the compiled array ABI

Status: FIXED 2026-11-15 on `work/engine2d-parity-4-20261115`.

## Symptom

`SIMPLE_VK_FONT_UPLOAD=u32` rendered a different pixel sum on forms-media
900x760 (`2697956136642868` vs the byte lane's `2697697746427296`). A
framebuffer diff showed 26,956 pixels off. These were not edge pixels: almost
every glyph on the page was missing. The heading "Interactive forms" and all
body text were gone, with only stray dots left.

## Root cause

The typed lane PARKS the atlas words and copies them at the next submit
(`font_atlas_drain_deferred_upload`). It sets `atlas_uploaded = true` at park
time.

`_vulkan_copy_to_buffer_u32_abi` declines whenever
`gpu_sffi_uses_interpreter_array_abi()` is false, and `simple run` on the seed
uses the compiled array ABI. So every drain failed:

    [vk-order] font-atlas-drain buffer=35 slot=0 words=1048576 rc=false
    [vk-order] cpu-fallback-first reason=atlas-deferred-upload-failed

By then the glyph dispatch was recorded against an empty atlas and could no
longer fall back to the byte path, so the run drew nothing. One "H" at 16 px
gave software ink 17 and Vulkan ink 0.

Under `SIMPLE_EXECUTION_MODE=interpret` the copy is admitted, and the u32 page
was already byte-identical to the byte lane (`cmp`: 0 bytes). The deferral
itself is sound; only the admission point was wrong.

The #9435 `clipped-out` return is NOT involved: with it disabled the u32 sum
was unchanged.

## Fix

`vulkan_sffi_copy_to_buffer_u32_admitted()` (sffi_vulkan.spl) answers the same
question the copy will. The font lane parks only when the typed upload is both
requested and admitted. Otherwise it takes the byte path and notes
`typed-declined`.

## Evidence

- `backend_vulkan_font_typed_upload_spec`: a live row checks that the predicate
  equals the real copy result on llvmpipe. Red: the predicate did not exist.
  Green: 5/5.
- forms-media 900x760, default run mode, seed 59635056 B, mtime 1794616340:
  the u32 framebuffer is now byte-identical to the byte lane (`cmp` 0 bytes,
  previously 80,868), and the byte lane is unchanged.
- `vulkan_text_advances_clip_parity` 7/7, `vulkan_font_atlas_overflow_parity`
  2/2, `vulkan_font_atlas_incremental_repack` 30/30.

## Open

The lane is still not usable as the default under the compiled ABI. There it
now always declines to bytes, because no `_array` twin of
`rt_vulkan_copy_to_buffer_u32` exists. Before making it the default, add that
twin and re-run this diff.
