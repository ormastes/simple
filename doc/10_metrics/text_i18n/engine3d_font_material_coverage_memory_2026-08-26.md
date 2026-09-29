# Engine3D font material coverage and memory — 2026-08-26

The bounded backend-neutral `font_hud_material.spl` owner now passes 9/9 with
100% lines (28/28) and 100% branches (6/6). Tests cover HUD and world vertex
layouts, depth conversion and rejection, shared Metal bytes, invalid batches,
undersized atlases, destination/atlas bounds, and vertex-size overflow. The
overflow arithmetic was extracted into `font_vertex_bytes_checked`, allowing
the guard to be tested without allocating roughly fifteen million quads.

The focused performance spec passes 1/1 over one immutable 64-quad batch:

- atlas CPU storage: 16,384 bytes;
- HUD output: 120 bytes/quad;
- world output: 144 bytes/quad;
- seven paired samples: 118,272 transient output bytes;
- observed HUD p50/p95: 133,464/139,525 us;
- observed world p50/p95: 181,091/189,761 us;
- whole-process HWM: 121,384 KiB;
- checksum: 1,785.

The byte counts and checksum are retained structural evidence. Timing and HWM
are smoke observations only: host load was 18.76/34.71/31.18 with a 32-thread
bootstrap, multiple multi-GiB compiler/test processes, and a Git pack active.
Allocation count, device memory, upload, queue completion, and readback remain
unavailable. This row does not qualify native Engine3D performance or GPU memory.

Scoped lint completed with zero errors; warnings are existing material/test style
issues and the new performance describe docstring was added afterward. The O3
optimizer audit reported 18 opportunities (11 bounds-check eliminations, five
dead-code eliminations, one loop-invariant motion, one constant fold). Those
estimates are not measured speedups and no optimizer rewrite was applied.
