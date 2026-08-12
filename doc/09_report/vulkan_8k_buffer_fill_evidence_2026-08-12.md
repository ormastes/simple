# Vulkan 8K Buffer-Fill Evidence — 2026-08-12

Status: **FAIL for full 8K/80; PASS for reproducible native-boundary evidence**

The standalone Vulkan boundary records one 132,710,400-byte framebuffer-sized
`vkCmdFillBuffer`, then measures each queue submission through fence completion.
Timing excludes readback. A separate full evidence readback verifies every
active pixel equals `0x000000ff` with zero mismatches and checksum
`17838657423967716227`.

Pinned ICD: Mesa llvmpipe, LLVM 20.1.2, 256 bits. Vulkan device type is 4
(`VK_PHYSICAL_DEVICE_TYPE_CPU`), so these measurements are software Vulkan and
must not be promoted as physical-GPU performance.

| Active 8K pixels | p50 ns | p95 ns | Isolated 12.5 ms budget |
|---:|---:|---:|---:|
| 5% | 570,740 | 671,121 | PASS |
| 25% | 3,462,621 | 3,633,998 | PASS |
| 50% | 7,040,352 | 7,353,049 | PASS |
| 75% | 11,263,113 | 11,958,752 | PASS |
| 80% | 11,727,811 | 11,892,886 | PASS |
| 85% | 13,200,963 | 13,430,051 | FAIL |
| 90% | 11,665,802 | 13,984,959 | FAIL |
| 100% (canonical wrapper, 31 samples) | 13,061,745 | 13,685,485 | FAIL |

The conservative isolated llvmpipe active-byte envelope is 80%. This operation
is a transfer fill, not an Engine2D compute shader or complete dynamic frame.
There is no swapchain/surface, presentation, DrawIR traversal, compositing, or
display scanout. The receipt therefore emits
`vulkan_8k_dynamic_frame_80fps_proven=false` and
`vulkan_8k_swapchain_presented=false` even when an isolated partial fill is
within budget. Evidence readback is 132,710,400 bytes but occurs after timing;
timed readback bytes are exactly zero.

Reproduce with `scripts/check/check-vulkan-8k-buffer-fill.shs`. Override
`VK_ICD_FILENAMES` to measure another explicitly identified ICD and use
`VULKAN_BENCH_ACTIVE_BASIS_POINTS` for retained active-area sweeps.
