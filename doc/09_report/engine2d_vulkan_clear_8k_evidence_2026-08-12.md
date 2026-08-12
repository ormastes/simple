# Engine2D Vulkan Clear 8K Evidence — 2026-08-12

Status: **FAIL full-frame 8K/80; PASS retained compute evidence**

This gate links directly to the Vulkan-enabled `simple-runtime` ABI and follows
the Engine2D clear lifecycle: 132,710,400-byte storage buffer, 256-thread clear
compute SPIR-V, 64-byte push constants, descriptor binding, command recording,
dispatch, fenced submission/wait, and dependency cleanup. Timing excludes
readback. A separate exact readback verifies zero mismatches and checksum
`11192757161153971075` for the full 8K frame.

Pinned llvmpipe measurements (15 samples):

| Active pixels | p50 ns | p95 ns | Isolated 12.5 ms budget |
|---:|---:|---:|---:|
| 5% | 1,099,999 | 1,545,870 | PASS |
| 25% | 5,275,748 | 6,906,621 | PASS |
| 50% | 8,862,893 | 12,218,878 | PASS |
| 75% | 19,708,381 | 23,437,297 | FAIL |
| 100% (canonical wrapper) | 22,629,394 | 25,944,270 | FAIL |

The conservative isolated retained envelope is 50% on this software Vulkan
device. This is a real Engine2D-compatible compute dispatch, but not a complete
DrawIR frame: there is no traversal, multiple primitives, presentation owner,
swapchain, or scanout. llvmpipe is CPU Vulkan, not physical-GPU evidence. The
receipt therefore reports zero timed readback bytes while keeping
`swapchain_presented=false` and `dynamic_frame_80fps_proven=false`.

Reproduce with `scripts/check/check-engine2d-vulkan-clear-8k.shs`; set
`ENGINE2D_VULKAN_ACTIVE_BASIS_POINTS` for retained sweeps and
`VK_ICD_FILENAMES` for an explicitly selected device ICD.
