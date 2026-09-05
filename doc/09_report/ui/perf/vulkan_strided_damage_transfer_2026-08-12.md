# Vulkan strided damage-transfer evidence — 2026-08-12

Status: **CORRECTNESS PASS / 8K80 NOT PROVEN**

Revision baseline: `27dfef19cca` plus the working-tree changes listed below.

## Implemented path

- `VulkanBuffer::{download_strided,upload_strided}` creates one staging buffer
  and submits one `vk::BufferCopy` region list for all rows.
- Raw and interpreter-returning SFFI entry points validate checked row layout.
- `VulkanBackend.present_damage_plan` reads exact `DamageFramePlan` rectangles,
  commits the host mirror only after every transfer succeeds, and records exact
  bytes/rectangles without calling a host copy a device present.
- Masked image host fallback uploads only its clipped rectangle. A failed
  strided upload uses an explicitly counted full-frame correctness fallback.

## Executed evidence

Pinned ICD: `/usr/share/vulkan/icd.d/lvp_icd.json`.
Device: llvmpipe (CPU Vulkan), Vulkan 1.3.275.

`native_vulkan_strided_round_trip_preserves_surrounding_rows` passed on the
live Vulkan runtime: two packed 3-byte rows were uploaded at noncontiguous
offsets, returned by both strided read APIs, and all surrounding sentinel bytes
remained unchanged. Result: 1 passed, 0 failed.

The backend and SFFI Simple source checks passed. O3 analysis completed for both
touched Simple modules. `git diff --check` passed.

## Honest performance status

This proves exact native transfer semantics and O(damage-bytes) device traffic;
it is not physical-GPU presentation evidence. There is still no swapchain
present path, no physical GPU row, and no 7680x4320 dynamic p50/p95/RSS/checksum
receipt. Therefore this lane cannot claim 8K at 80 FPS. The next evidence gate
is a native Engine2D damaged-frame benchmark with dispatch, transfer, fallback,
readback and checksum receipts, followed by a physical GPU run.
