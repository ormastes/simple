# Simple WM Host and SimpleOS Fullscreen NFRs

**Selection:** NFR Target 1, selected 2026-07-11.

- **NFR-1:** After one discarded launch, each of 10 warm production host WM launches shall reach first presented shared-scene frame within 2 seconds on the recorded reference host.
- **NFR-2:** Over 30 enter/exit pairs, request-to-acknowledged-physical-state response shall be <=250 ms p95, excluding platform visual animation.
- **NFR-3:** After 60 discarded frames, nearest-rank p95 over 600 1920x1080 frames shall be <=16.7 ms for an accelerated row; an explicitly requested typed fallback row shall be <=50 ms.
- **NFR-4:** Over 30 pairs on the documented fixed QEMU machine/CPU/RAM configuration at idle load, emulated-device input submission to matching framebuffer generation shall be <=500 ms p95.
- **NFR-5:** After 100 host transition pairs, final RSS shall be <= baseline + max(16 MiB, 5%) and least-squares RSS slope over the final 50 samples shall be nonpositive.
- **NFR-6:** Every performance row records renderer/backend, fallback, viewport, revision, executable hash/version, readback, and checksum.
- **NFR-7:** Unverified captures, stale reports, missing dependencies, seed provenance, fixed scanout metadata, or silent fallback block PASS.
- **NFR-8:** At scales 1.0/1.5/2.0/3.0 and 1280x720/1920x1080/3840x2160/7680x4320, rendering consumes physical resize/scale events, has no chrome/taskbar overlap, keeps every hit target >=44 logical px, bounds title glyph ink, and retains nonzero clipped content rects.
