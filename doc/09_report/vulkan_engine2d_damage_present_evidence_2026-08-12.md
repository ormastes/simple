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
- Direct environment guards: PASS.
- Simple optimizer O3 checks for the modified backend and SFFI wrapper: PASS.

At 7680x4320 ARGB, a full transfer is 132,710,400 bytes. The same 3x2 damage is
24 bytes after history seeding. This is structural byte accounting, not an 8K
timing measurement.

## Honest Scope

Lavapipe is a CPU Vulkan implementation and the live fixture is intentionally
small. This evidence proves functional region submission, conservative
swapchain-image history handling, and exact transfer receipts. It does not
prove physical-GPU throughput, swapchain scanout, or the 8K/80 performance
target. Those remain separate hardware evidence gates.
