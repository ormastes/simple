# Vulkan Engine2D Damage-Present Evidence — 2026-08-12

## Result

The retained swapchain path now copies exact damaged rectangles after each
rotating image has a valid revision history. A missing or incomplete history
fails safe to a full-frame seed. Backend receipts report the device-to-present
byte and rectangle counts produced by the native copy.

## Verification

- Pure revision-history test: PASS. Exact regions are retained across missed
  revisions; missing, empty, invalid, or excessive history requests a full copy.
- Headless lavapipe live test (64x32): PASS. After safe image seeding, a 3x2
  rectangle reports one device-to-present region and exactly 24 bytes.
- Headless lavapipe 8K damage benchmark: PASS against the 12.5 ms frame budget.
  Twenty changing revisions with a 7680x43 rectangle (330,240 pixels, about
  0.995% of the viewport) measured p50 280,847 ns and p95 314,010 ns. Each
  frame reported one region, exactly 1,320,960 device-to-present bytes, zero
  readback bytes, known completion, and no fallback. Peak RSS was 580,168 KiB;
  source-buffer checksum was 15184660652564333443.
- Direct environment guards: PASS.
- Simple optimizer O3 checks for the modified backend and SFFI wrapper: PASS.

At 7680x4320 ARGB, a full transfer is 132,710,400 bytes. The same 3x2 damage is
24 bytes after history seeding. This is structural byte accounting, not an 8K
timing measurement.

## Honest Scope

Lavapipe is a CPU Vulkan implementation. The small fixture proves region
correctness; the 8K fixture proves headless damaged-present timing and exact
transfer accounting for this narrow workload. Its checksum covers the immutable
source buffer rather than post-scanout pixels. This evidence does not prove
physical-GPU throughput or physical-display scanout. Those remain separate
hardware evidence gates.

## 2026-08-13 native transfer recheck

The native Rust runtime transfer test passed against the pinned llvmpipe ICD:

```text
cargo test --locked --offline -p simple-runtime --features vulkan \
  vulkan_graphics_runtime::vulkan_graphics_runtime_buffer::tests::native_vulkan_upload_honors_nonzero_offset \
  -- --ignored --exact
result: 1 passed
```

That test performs a nonzero-offset upload, a packed strided read, and a
two-region packed read in one native runtime session. It verifies the exact
range/region mechanism used by damaged host-cache refreshes.

The authoritative Simple Engine2D readback script was also rerun with the
pinned llvmpipe ICD. Its clear and rectangle device readbacks had zero pixel
mismatches and concrete device identities, but the overall script status was
`fail` because `bin/simple` identified itself as a Rust bootstrap seed and
fell back to the interpreter for its requested native execution mode. The
focused strict/parity specs were intentionally not run after that provenance
gate. Consequently this recheck adds native runtime-transfer correctness only;
it does not refresh, replace, or extend the 8K/80 evidence claim above.
