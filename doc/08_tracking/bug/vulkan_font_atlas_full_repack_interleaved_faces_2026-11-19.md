# Vulkan font atlas is fully repacked on every run when two faces interleave

Status: OPEN (found by the Vulkan LCD batching lane, not fixed there: the
producer lives in `text_layout/font_renderer.spl`, owned by another lane).

## Measured (2026-11-19, lavapipe, seed `cargo-target-webrender-blend`)

900x760 page, 36 paragraphs alternating sans / serif (regular, bold, italic) /
monospace, one cold render, `SIMPLE_VK_TIMING=1`:

| lane | wall | `font_atlas_pack_u32_to_u8` | pack_full / incremental |
|---|---|---|---|
| cpu_simd | 29.9 s | - | - |
| Vulkan, default byte upload | 308.2 s | 286.6 s (60 calls, ~5 s each) | 60 / 0 |
| Vulkan, `SIMPLE_VK_FONT_UPLOAD=u32` | 24.2 s | 0 | 0 / 0 |

All three frames are byte-equal. Vulkan with the default upload is 10x slower
than the CPU backend, and all of it is the interpreted 1,048,576-pixel
`_vulkan_font_pixels_to_bytes` loop.

## Cause

`vulkan_font_mirror_continuity` (`backend_vulkan_helpers.spl`) allows the
incremental repack only when `batch.atlas_owner_sequence == host + 1`. With
`SIMPLE_VK_ORDER_TRACE=1` on a two-face page (sans and serif paragraphs
alternating, 3 each):

```
owner=Sans-Regular  slot_seq=6  host_seq_before=6  batch_seq=8  continuity=0 dirty=2
owner=Serif-Regular slot_seq=10 host_seq_before=10 batch_seq=12 continuity=0 dirty=2
owner=Sans-Regular  slot_seq=8  host_seq_before=8  batch_seq=10 continuity=0 dirty=2
```

The per-owner sequence moves by 2 between two batches of the same owner as soon
as another face draws in between, so the rule never holds and every run takes
`VK_FONT_MIRROR_FULL` (`pack_full=6 pack_incremental=0`). A one-face page moves
by 1 and repacks incrementally (`continuity=1`). Raising
`VULKAN_FONT_ATLAS_MIRROR_MAX` 4 -> 8 changes nothing (tried: 308.6 s, 60 / 0).

## Fix directions (not done)

1. Find what bumps `atlas_owner_sequence` a second time when faces interleave
   (producer side), so one dirty batch is one step again.
2. Or make the typed upload (`SIMPLE_VK_FONT_UPLOAD=u32`) the default where
   `vulkan_sffi_copy_to_buffer_u32_admitted()` holds; it has no host pack at all.

Do not relax the `+1` rule on the consumer side: a gap can also mean a dirty
batch that never reached the backend, whose cells the mirror would be missing.
