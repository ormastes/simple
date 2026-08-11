# Complete the GPU layout semantic/device boundary

Status: OPEN — concrete boundary and bounded device slices implemented

The layout framework must not publish `hybrid_vector_gpu` from policy or
oracle copying.

Implemented on 2026-07-31:

- typed topology, box, flex, grid, viewport, track, and admission contracts;
- CPU-oracle boxes moved to a snapshot verification channel rather than node
  semantics;
- a CUDA consumer port with real semantic upload, PTX dispatch,
  synchronization, geometry readback, and exact oracle comparison;
- pre-dispatch rejection for unsupported semantics; and
- live fixed-root and one-level block/flex/grid device evidence;
- bounded absolute positioning and overflow/scroll extent kernels; and
- Latin line-break dispatch with complex-script pre-submission rejection.

Remaining fix:

1. Run the WPT-derived parity corpus with the production self-hosted CLI when
   a complete Stage4 binary is available.
2. Expand beyond the intentionally bounded one-level/fixed-track GPU admission
   slice only as new parity cases require it.
3. Add shaped complex-script line breaking after a semantic shaping contract
   exists; those scripts currently reject before GPU submission.

Outside the implemented slice, GPU remains a candidate and falls back with an
explicit reason before device submission.

## 2026-08-09 re-verification (worktree agent)

Re-read this doc against the current worktree; no `bin/simple` self-hosted
binary is deployed there (gitignored symlink target, as expected for an
isolated worktree) and the doc's own remaining item 1 explicitly requires "the
production self-hosted CLI when a complete Stage4 binary is available" — that
precondition is unmet here and in the main repo alike. Items 2 and 3
(expanding the bounded GPU admission slice; shaped complex-script line
breaking pending a semantic shaping contract) are scoped feature growth, not
defects with a bounded root-cause fix. **Confirmed ARCHITECTURAL-OPEN** —
status and remaining-work list left unchanged as an accurate characterization;
no code change made.
