# Vulkan strided transfer live evidence — 2026-08-11

## Attempt

Focused command, pinned to lavapipe:

```sh
VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/lvp_icd.json \
  cargo test -p simple-runtime --features vulkan \
  native_vulkan_strided_read_packs_nonzero_offset_rows -- --ignored --nocapture
```

## Result

**PASS for live lavapipe sparse strided transfer.** The three stale public ABI
exports were restored against the value layer's unified `WideInt`
representation. `cargo check -p simple-runtime --features vulkan
--no-default-features` completed, and the live nonzero-offset packed-row test
passed 1/1 against `/usr/share/vulkan/icd.d/lvp_icd.json`.

The 8K-buffer/64x64-damage test then passed 1/1 over 200 samples:

| viewport | damage | bytes/direction | read p50/p95 | upload p50/p95 | budget |
|---|---:|---:|---:|---:|---:|
| 7680x4320 | 64x64 | 16,384 | 1.455/1.994 ms | 1.312/1.410 ms | 12.5 ms |

Checksum was 1,474,560 and the test completed with zero assertion failures.
The result proves a sparse transfer primitive on a CPU Vulkan implementation;
it is not a physical-GPU or full rendering/presentation pass.

## Current implementation audit

`VulkanBuffer::upload_strided` and `download_strided` construct one
`vk::BufferCopy` region per row, use one staging allocation, and issue one
transfer submission per rectangle. `download_range` copies the requested range
rather than the entire prefix. These are materially better transfer semantics
than the former row-by-row/prefix-copy implementation, but source inspection is
not live performance evidence.

The ignored test named
`native_vulkan_8k_strided_read_meets_80fps_transfer_budget` allocates a
7680×4320 buffer but measures only a 64×64 rectangle (16,384 bytes) over 200
samples. It does not measure full-frame rendering, swapchain presentation, or a
physical GPU. Its initial 64 row uploads occur outside the measured read loop.
Even when green, this test may support only a sparse-damage transfer receipt.

## Promotion requirements

Before any 8K/80 claim:

1. Run the same tests on the NVIDIA device and record device/driver identity.
2. Feed exact damage rectangles through Engine2D and DrawIR production calls.
3. Complete a real swapchain/device-surface present with known completion.
4. Record p50/p95, bytes transferred, dispatch/submission/fence counts,
   fallback state, RSS, and device pixel checksum evidence.
5. Pass `scripts/check/check-render-8k80-receipt.shs`; composition-only or
   host-cache receipts remain insufficient.

## Swapchain presenter hardening update

The canonical Engine2D swapchain bridge structural spec passes 4/4. During the
review, `rt_vk_engine2d_presenter_present` was found to return success when
`acquire_next_image` reported `SUBOPTIMAL`, without copying or presenting the
usable acquired image. That false-positive path is removed: suboptimal images
now continue through the on-device buffer-to-image copy and queue present.

The focused runtime test command

```sh
cargo test -p simple-runtime --features vulkan swapchain::tests -- --nocapture
```

is no longer blocked by the missing exports.

## Live swapchain receipt

The ignored production-bridge probe passed 1/1 on Xvfb `:99` with the pinned
lavapipe ICD after fixing two window-owner defects: Linux event-loop creation
now explicitly permits its designed background thread, and the loop remains
alive until an explicit shutdown request instead of exiting on its initial
empty idle tick.

```text
VULKAN_ENGINE2D_DEVICE_PRESENT viewport=64x64 bytes=16384 elapsed_ns=401397 presenter=3 buffer=1 status=0 checksum=2457600
```

This is direct evidence that the canonical bridge acquired a swapchain image,
copied the live Engine2D device buffer, and successfully queued presentation.
It is a 64x64 llvmpipe/Xvfb functional receipt, not physical-GPU evidence and
not an 8K/80 performance result. The full retained/dynamic 8K matrix therefore
remains open.

## Full 8K present and retained frame-switch results

The production bridge was then measured on an actual 7680x4320 Xvfb surface
with the pinned llvmpipe ICD. A 20-frame dynamic present copied all 132,710,400
bytes on every frame and passed correctness, but failed the 12.5 ms budget:

| mode | frames | copy bytes/frame | p50 | p95 | 80 fps |
|---|---:|---:|---:|---:|---|
| dynamic full copy | 20 | 132,710,400 | 102.122 ms | 204.973 ms | FAIL |
| retained, FIFO | 80 | 0 | 69.457 ms | 88.956 ms | FAIL |
| retained, low-latency request | 80 | 0 | 74.394 ms | 96.942 ms | FAIL |
| dynamic 64x64 damage history | 80 | <=65,536 | 66.395 ms | 78.413 ms | FAIL |

The retained path uses a per-swapchain-image revision table. After all images
are seeded, every measured call returned status `2`, proving exact image reuse
with no buffer-to-image copy. The low-latency presenter explicitly requests
IMMEDIATE mode while preserving the default vsynced API, but this software
X11/Vulkan stack still spends far beyond budget in acquire/queue-present.

Checksums were 11,943,936,000 for the dynamic fill and 21,897,216,000 for the
retained fill; fallback was false and completion was known. These results prove
that frame switching alone does not make llvmpipe/Xvfb achieve 8K/80. A
physical-GPU WSI run remains required, and dynamic full-copy presentation still
needs partial-damage or direct render-to-swapchain work.

## Dynamic damage-chain update

The production presenter now retains a bounded chain of frame revisions and
their exact damage rectangles. For each acquired swapchain image it combines
all intervening deltas from that image's own revision, submits the regions in
one buffer-to-image transfer command, and updates the image revision only after
successful presentation. A missing or discontinuous chain fails closed to a
full-frame copy.

The live 8K test moved one 64x64 region for 80 sequential revisions across the
multi-image swapchain. Every measured frame returned the partial-copy receipt;
there were zero full fallbacks, at most four accumulated rectangles, and at
most 65,536 copied bytes versus 132,710,400 bytes for a full frame. A sabotage
call with an intentionally stale base revision returned the explicit full-copy
status and recorded exactly 132,710,400 bytes.

Correctness and transfer scaling pass, but the llvmpipe/Xvfb WSI path remains
the dominant cost and still fails 80 fps. This separates the production
damage-copy optimization from the unresolved physical presentation gate.

Acquisition now always supplies valid Vulkan synchronization: callers without
a semaphore receive a temporary unsignaled fence, and the owner waits that
fence before recording the image transfer. The live damage test remained green
after this hardening. The showcase Vulkan host now creates the presentation
owner before Engine2D resources, adopts that exact device, and requires a real
swapchain-present status before publishing `device_present=true`.

## DrawIR no-readback production seam

DrawIR now has an additive fenced submit-only entry point. It neither calls
backend `present()` nor requests framebuffer pixels. A healthy Vulkan engine
publishes its device framebuffer handle and device identity only while no CPU
fallback or unknown completion is active; the submit result records
`device_submit_no_readback` with one accepted submit and fence receipt.

The Vulkan showcase host uses an explicit verification cadence: its first frame
still takes the strict full device readback and checksum path. Later changed
frames use submit-only plus swapchain presentation, while identical frames skip
DrawIR execution and use retained presentation. A changed, unverified frame
does not masquerade as captured pixels. The focused source contract passes 3/3
and the host source passes `simple check`; live performance is not promoted
until a freshly deployed self-hosted runtime exercises this new Simple-to-Rust
path.

The first focused deployment attempt was stopped after more than ten minutes:
the native-build worker remained at 100% CPU, emitted no stage progress, and
produced no executable. It was not retried. The build-performance defect is
tracked in
`doc/08_tracking/bug/vulkan_drawir_showcase_native_build_exceeds_10m_2026-08-11.md`;
therefore the live no-readback showcase gate remains explicitly not run.

## Hosted WM existing-window seam

The hosted WM can now create the Vulkan presentation owner from the native
Xlib or Wayland handles of its existing winit window. The external presenter
adopts that surface without owning or destroying the winit window, and it is
created before Engine2D so both sides share the canonical Vulkan device.
Hosted presentation tries the device path first and preserves the existing
software-pixel presenter as a fail-closed fallback.

The focused ownership/fallback contract passes 3/3. Both Rust crates compile:
`spl_winit` and `simple-runtime` with the Vulkan feature. The focused Simple
check of `hosted_entry.spl` reached the repository's 60-second CPU guard before
emitting a source diagnostic, so Simple compilation and live WM performance
are not claimed here.

The compositor now selects DrawIR's fenced submit-only entry point whenever
the existing-window Vulkan presenter is active. A valid no-readback result
requires the exact device source label, nonzero framebuffer/device identities,
and one submit plus one fence receipt. It bypasses the headless compositor
blit. If device presentation fails, the software presenter explicitly reads
the authoritative Engine2D framebuffer; evidence capture does the same, so
neither path can silently consume the stale compositor mirror. The strengthened
contract remains 3/3. O3 optimizer analysis completed for all three changed
Simple modules. A single combined source-check attempt with a 180-second guard
timed out inside the checker without a source diagnostic, so this remains
source-contract evidence rather than a live zero-readback WM performance row.

WM damage ownership is now connected as well: immediately before DrawIR
submission, the host compositor clears the executor's prior frame damage and
forwards every rectangle from its canonical `DirtyRegion`. The executor clips
those rectangles, and the revision-aware presenter applies its existing
initial-frame, invalid-chain, area, and malformed-plan full-copy fallbacks.
After this addition the focused contract again passes 3/3. This proves the
source-level ownership chain; exact live transfer-byte receipts still require
the blocked native deployment.

The executor-specific check was then rerun after the explicit fallback and
evidence readback receipt update and passed:
`simple check src/os/compositor/compositor_engine2d.spl`. The exceptional
readback now records its actual source, handle, checksum, dimensions, and
format; steady Vulkan frames retain `device_submit_no_readback`. This closes
the source-level provenance gap but does not replace the still-required native
hosted-WM 8K measurement.

The independent `host_compositor_core.spl` checker run reached its configured
180-second watchdog without a source diagnostic and was not retried. The
focused 3/3 contract and the executor check remain the completed source-level
verification for this change; they must not be mistaken for deployed 8K
evidence.
