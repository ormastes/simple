# Simple2D macOS emulator contract status — 2026-08-09

The macOS lane is a static, readiness-only emulator contract on Linux. It does
not claim a native macOS window, GPU execution, or performance result.

The lane reuses the shared `DrawIrComposition` and Vulkan differential
admission path. It has no Metal requirement and introduces no macOS-private
renderer. Promotion remains fail-closed until one prepared macOS environment
provides a single correlated trace containing:

- 20 animation frames;
- pointer move/down/drag/up/wheel and key down/up with left/right Ctrl and Alt;
- canonical font batch plus atlas upload;
- audio submit plus completion;
- frame capture;
- Vulkan submit, fence, and device-origin readback;
- stable device identity, no fallback, p95 latency, and maximum RSS.

Linux can verify the profile, trace validator, negative missing-receipt cases,
and readiness-only admission. It cannot close TODO 660 or supply live macOS
evidence. Metal receipts and Linux/QEMU framebuffer readback are explicitly
inadmissible substitutes for this lane.
