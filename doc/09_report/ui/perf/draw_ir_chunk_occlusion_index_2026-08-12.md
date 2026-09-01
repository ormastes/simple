# DrawIR chunk-occlusion index evidence — 2026-08-12

Status: **CORRECTNESS PASS / STRUCTURAL SPEEDUP / 8K80 NOT PROVEN**

`chunk_occlusion.spl` previously tested every later paint chunk for every
candidate, even when most later chunks lacked an exact opaque proof. The
workspace now owns a reusable reverse linked index of visible exact-opaque
chunks. Exact rectangle subtraction, surface isolation, paint order, overflow
fail-open behavior, and the public result remain unchanged.

The focused unit suite passed, including optimized-versus-unoptimized full
pixel-buffer parity. Its 64-transparent-plus-one-opaque adversarial scene now
examines exactly 64 candidate slots instead of the previous triangular 2,080,
a 32.5x structural reduction. All 64 covered chunks are still culled.

The index is additionally partitioned by render-surface identity through a
preallocated open-addressed surface-head table. A 32-chunk alternating-surface
scene now examines 240 same-surface links instead of 496 global-chain links;
every stored link was asserted to retain identical surface ownership. This
prevents independent offscreen/render-target batches from consuming each
other's occlusion budget.

Each opaque-chain node now also carries a reusable suffix-union bound. When
that conservative bound is disjoint from a candidate, the complete later chain
is rejected before any per-occluder visit. In the same 32-chunk disjoint scene,
visits fall from the original 496 to **0**, with 30 whole-chain rejections.
The mixed disjoint-plus-late-overlap oracle remains pixel-identical, proving
that a broad suffix bound does not substitute for exact subtraction when an
intersection is possible.

O3 analysis completed and reported 97 further compiler opportunities. The
general source checker itself reached the repository's 60-second CPU guard
without a code diagnostic; it was not retried. This mechanism result is not an
8K frame-time row and makes no 8K/80 claim.
