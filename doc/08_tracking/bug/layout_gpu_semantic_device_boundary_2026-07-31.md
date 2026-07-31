# Complete the GPU layout semantic/device boundary

Status: OPEN — concrete boundary and fixed-leaf device slice implemented

The layout framework must not publish `hybrid_vector_gpu` from policy or
oracle copying.

Implemented on 2026-07-31:

- typed topology, box, flex, grid, viewport, track, and admission contracts;
- CPU-oracle boxes moved to a snapshot verification channel rather than node
  semantics;
- a CUDA consumer port with real semantic upload, PTX dispatch,
  synchronization, geometry readback, and exact oracle comparison;
- pre-dispatch rejection for unsupported semantics; and
- live fixed-leaf block/flex/grid device evidence.

Required fix:

Remaining fix:

1. Extend the kernel admission slice from fixed childless roots to block child
   stacking, fixed flex row/column children, and fixed grid tracks/placement.
2. Add absolute placement, overflow/clipping, and supported-script line-break
   phases required by `web_layout_manager_plan.md`.
3. Qualify the expanded slices against the WPT-derived parity corpus.

Outside the implemented slice, GPU remains a candidate and falls back with an
explicit reason before device submission.
