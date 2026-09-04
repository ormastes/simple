# Engine2D C Vulkan 8K evidence — Apple M4 — 2026-09-04

The portable C baseline ran through MoltenVK 1.4.1 on the physical integrated
Apple M4 at 7680x4320. Every accepted row used 31 samples, known fence
completion, zero timed readback, zero pixel mismatches, and no fallback.

| Feature | Work | p50 | p95 | 80 fps |
|---|---:|---:|---:|---|
| filled rectangle | 331,776 pixels | 0.423 ms | 0.477 ms | PASS |
| 16 horizontal generic lines | 16 x 7,680 pixels | 9.492 ms | 10.174 ms | PASS |
| 16 horizontal lines as rectangles | 16 x 7,680 pixels | 0.630 ms | 1.229 ms | PASS |
| image upload/copy | 331,776 pixels | 0.909 ms | 1.511 ms | PASS |
| packed font atlas | 64 x 16x16 glyphs | 0.689 ms | 0.934 ms | PASS |
| retained mixed frame | rect + image + 1,024 glyphs + 16 lines | 1.175 ms | 1.280 ms | PASS |

The additional full-frame image upload/copy stress row was exact but missed
the budget: p50 16.772 ms and p95 21.506 ms. It is not substituted for the
matched 1% image parity workload. The result identifies a persistent-image
resource requirement; uploading 132,710,400 source bytes every frame is not an
80 fps rendering architecture.

The retained mixed row validates the intended remedy on the same device. It
uploads its image source before timing, then records 19 dispatches in one
submission with zero timed readback. At 1.280 ms p95 it is 16.8x faster than
the full-frame re-upload stress row while still producing an exact final 8K
checksum.

The generic-line result also validates the existing Simple Vulkan fast path:
one-pixel axis-aligned lines must lower to parallel filled rectangles. The C
rectangle lowering was 8.3x faster at p95 than its ordered generic line shader.

Simple/C ratios remain pending until an admitted self-hosted compiler produces
the Simple feature executables. Bootstrap artifacts are rejected by the parity
runners, so these C measurements are baselines rather than parity claims.
