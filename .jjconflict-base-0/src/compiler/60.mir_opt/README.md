# MIR Optimization Group

This folder is the grouped home for MIR optimization inventory and level guidance.

## Canonical Pipeline

The canonical pass pipeline currently lives in:

- [`mir_opt/mod.spl`](./mir_opt/mod.spl)
- [`mir_opt/__init__.spl`](./mir_opt/__init__.spl)
- [`mir_opt_integration.spl`](./mir_opt_integration.spl)

This pipeline defines the public `OptLevel` values and the pass lists used for:

- `Size`
- `Speed`
- `Aggressive`

Representative pass groups in that pipeline:

- cleanup: dead code elimination
- scalar: constant folding, copy propagation, global value numbering, common subexpression elimination
- control flow: tail-call optimization, outlining
- loop: LICM, loop optimization, strength reduction
- vectorization/SIMD: vectorization analysis and lowering
- data/path specialization: collection optimization, string builder optimization, generator state machine

## Legacy Engine

[`optimization_passes.spl`](./optimization_passes.spl) is a separate older optimization engine with its own `OptimizationLevel` and `OptimizationEngine`.

That file is still useful implementation history, but it is **not** the best source of truth for current level-to-pass mapping. The `mir_opt/mod.spl` pipeline should be treated as canonical for pass inventory and level grouping unless or until the duplication is removed.

## Relationship To Other Optimization Groups

- Syntax optimization guidance is grouped under `src/compiler/10.frontend/syntax_opt/`.
- Repo-level optimization guidance is documented in [`doc/07_guide/compiler_optimization_levels.md`](../../../doc/07_guide/compiler_optimization_levels.md).
