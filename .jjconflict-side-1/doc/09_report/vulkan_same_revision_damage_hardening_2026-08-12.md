# Vulkan Same-Revision Damage Hardening — 2026-08-12

Status: **LIVE CORRECTNESS PASS / FRAME-SWITCH PRESERVED / 8K80 UNCHANGED**

## Defect and fix

The swapchain presenter previously skipped its device-buffer copy whenever the
acquired image already carried the requested content revision. That is valid for
an unchanged frame, but not for a nonempty damage request: a caller may reuse a
revision while reporting changed pixels. The old route presented stale image
content with zero transfer telemetry.

The no-copy route now requires both an equal revision and empty damage. Equal
revision with nonempty damage cannot derive an ordered delta from revision
history, so it fails safe to one full-frame copy. Empty-damage retained frame
switching remains zero-copy.

## Live lavapipe evidence

- Same revision plus a nonempty 1x1 damage descriptor: PASS. The presenter
  returned full-copy status, reported one rectangle, and copied the exact
  `64 * 32 * 4 = 8192` bytes.
- Same revision plus empty damage: PASS. The second presentation reported zero
  copied bytes and zero copied rectangles.
- Both tests used the pinned lavapipe ICD and real headless swapchain calls.

Lavapipe is a CPU Vulkan implementation. This change closes stale-frame receipt
correctness and preserves idle frame-switching; it does not add or change an 8K
throughput claim or prove physical display scanout.
