# Vulkan 8K full-frame image re-upload misses 80 fps

## Status

Open; measured on 2026-09-04.

## Evidence

The physical Apple M4 MoltenVK C reference uploaded and copied a 7680x4320
RGBA source inside every timed frame. With 31 samples it produced p50 16.772 ms
and p95 21.506 ms, zero mismatches, known completion, and zero timed readback.
The 12.5 ms 80 fps gate therefore failed. The matched 1% image row passed at
1.511 ms p95.

## Required fix

Engine2D needs an owner-scoped persistent Vulkan image resource whose upload is
separate from repeated composition. Creation or explicit update may upload;
unchanged frame composition must bind and reuse the retained device image.
Resource generation, destruction, device ownership, fallback state, and source
mutation invalidation must remain inside the Vulkan backend owner.

Admission requires a new full-8K retained-image C/Simple workload with identical
device identity and checksum, zero timed upload/readback, known completion, no
fallback, p95 at or below 12.5 ms, and Simple p95 at most twice C p95. Merely
moving upload outside the timer without exposing retained-resource semantics is
not acceptable evidence.
