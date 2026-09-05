# Engine3D Vulkan font adapter coverage and memory — 2026-08-26

The focused fail-closed suite passes 4/4. Across three bounded cycles, direct
coverage improved from 29% lines (29/97) and 0/6 decisions to 35% lines (34/97)
and 12% branches (1/8). It covers upload invalidation, invalid dimensions,
unavailable evidence, command/reentry guards, invalid material, and shutdown.
No 100% claim is made.

The pure-Simple child reports unavailable Vulkan SFFI imports and adapter
creation returns `vulkan-font-adapter-init-failed`. Consequently no native
pipeline, atlas upload/reuse, HUD/world draw, queue/fence completion, device
readback, or device-loss path executed.

Status: `unavailable:required-vulkan-sffi-and-device-path-not-active`.

Required future memory-performance evidence: cold/warm atlas bytes and uploads,
transient vertex/staging allocations, steady/peak RSS delta, VRAM high-water,
draw calls, queue/fence/readback latency, pixel checksum, and post-shutdown
retention. Fail-closed CPU coverage is not a native-device performance receipt.
