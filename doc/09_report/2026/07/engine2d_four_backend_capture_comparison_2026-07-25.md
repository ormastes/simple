# Engine2D Four-Backend Capture Comparison — 2026-07-25

STATUS: FAIL (live evidence remains fail-closed)

| Lane | Implementation | Live capture/events |
|---|---|---|
| Vulkan | Provider initialization and device discovery PASS | Native driver exits before receipt; no PPM/PNG |
| Metal | GPU-only readback, vector text, 300 DPI, and event source audit PASS | No admissible native executable; no PPM/PNG |
| Host SIMD | AArch64 NEON executed with positive hits and bit-exact scalar parity | Auxiliary facade timed out; no durable scene/event capture |
| QEMU x86_64 SIMD | Canonical wrapper selected the pure-Simple compiler | Native build timed out at 180 seconds before ELF/QEMU |
| QEMU ARM64 SIMD | Readiness, VirtIO preflight, NEON counters/parity, and strict guest receipts PASS statically | Target did not build; no live counters, framebuffer, or events |

The normalized contract now records scene ID, target-side event source, GPU
device-readback identity or SIMD hit/chunk/parity receipts, and rejects CPU
fallback, QMP-only delivery, metadata mismatch, and missing execution evidence.

No pair produced two admissible records, so no pixel tolerance result is
claimed. The aggregate comparison correctly rejects the run.

Verification was additionally blocked by a full data volume and concurrent
unrelated compiler/parser edits. Two abandoned native-build temporary object
directories were removed, recovering limited space; they are not recoverable.
