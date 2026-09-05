# Engine2D Four-Backend Capture Requirements

The user selected the complete four-lane implementation directly; no unchosen
option is retained.

## REQ-E2D4-001 — Shared scene

Metal, Vulkan, host CPU SIMD, x86_64 SimpleOS QEMU SIMD, and ARM64 SimpleOS
QEMU SIMD shall render the same deterministic scene description.

## REQ-E2D4-002 — Real backend execution

Each capture shall prove the requested backend executed. GPU lanes require
device-backed readback identity. SIMD lanes require native hit/chunk counters
greater than zero and bit-exact scalar-kernel parity.

## REQ-E2D4-003 — Ordered events

Each target shall receive `focus,pointer_move,pointer_down,pointer_up,key_down,
key_up` in that order. Injection and target-side delivery receipts shall be
recorded separately.

## REQ-E2D4-004 — Durable capture

Each target shall write a durable PPM or PNG capture plus width, height, DPI,
SHA-256, non-background bounds, source revision, target, and capture path.

## REQ-E2D4-005 — Comparison

The comparison shall report exact metadata/event equality and pixel mismatch
count, maximum channel delta, and accepted tolerance. A missing or invalid lane
shall make the aggregate result fail.

## REQ-E2D4-006 — Honest failure

Scalar fallback, CPU-mirror GPU evidence, QMP-only injection without guest
delivery, stale captures, or self-reported backend strings shall not pass.
