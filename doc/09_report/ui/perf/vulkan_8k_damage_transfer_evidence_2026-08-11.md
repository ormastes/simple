# Vulkan 8K damage-transfer evidence — 2026-08-11

Status: **LOCAL TRANSFER PASS ON LAVAPIPE; HARDWARE PRESENT PROOF OPEN**

## Production mechanism

The Vulkan storage-buffer backend supports one-submit packed strided upload and
download. `present_damage_plan` refreshes only exact LOCAL damage rectangles
into a seeded retained host mirror. NONE performs zero transfer. FULL, invalid,
or unseeded plans fail closed to the complete-frame path. Receipts explicitly
report `present_mode=host_cache` and never claim swapchain/device presentation.

## Live 8K transfer row

Pinned ICD: `/usr/share/vulkan/icd.d/lvp_icd.json` (llvmpipe CPU Vulkan).
Viewport: 7680x4320. Damage: 64x64 ARGB, 16,384 bytes. Frames: 200.

| Direction | p50 | p95 | 12.5 ms gate |
|---|---:|---:|---:|
| device to packed host | 1,180,691 ns | 1,370,153 ns | PASS |
| packed host to device | 1,187,002 ns | 1,345,005 ns | PASS |

Checksum: 1,474,560, exactly `16,384 * 0x5a`.

The current Cargo workspace could not rebuild because concurrently modified
value modules export three missing symbols. The already-built current Vulkan
test executable was therefore invoked directly; it ran the exact ignored test
`native_vulkan_8k_strided_read_meets_80fps_transfer_budget` and passed 1/1.

## Backend parity

`test/02_integration/rendering/vulkan_damage_present_spec.spl` on pinned
llvmpipe: **4 examples, 0 failures**. It proves exact 24-byte local transfer,
zero-byte idle reuse, unseeded full fallback, complete retained-buffer parity,
and exact masked host-fallback upload bounds.

## DrawIR production seam

`Engine2D.present_damage_plan` now dispatches the exact plan to a concrete
Vulkan target. The retained DrawIR composition executor uses that method for
LOCAL damage instead of ordinary `present()` (which performs a full storage
buffer read). Conservative offscreen/parent-sampling fallback constructs an
explicit full-surface plan, so it cannot accidentally claim a partial transfer.
Other Engine2D backends preserve their canonical present behavior.

Pinned-llvmpipe DrawIR composition gate: **5 examples, 0 failures**. Its live
Vulkan case seeds the mirror, replays a 2x3 clip, presents through the production
seam, asserts exactly 24 transferred bytes / one rectangle / no full-frame
transfer, then compares the complete framebuffer including outside sentinels.
The complementary translucent-composition case proves fail-closed behavior:
an offered LOCAL plan becomes an explicit 256-byte full-frame transfer.

## Claim boundary

This proves that a small damaged transfer fits an 80 fps transfer budget on
software Vulkan. It does not prove full dynamic rendering, physical-GPU
throughput, swapchain presentation, display scanout, or aggregate 8K/80 frame
latency. A full-frame comparison row is still missing.
