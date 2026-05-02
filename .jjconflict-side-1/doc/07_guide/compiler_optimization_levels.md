# Compiler Optimization Levels

**Date:** 2026-04-29

This guide centralizes what optimization groups currently exist and how native executable builds use them.

## Groups

### Syntax optimization

Grouped under [src/compiler/10.frontend/syntax_opt/README.md](/home/ormastes/dev/pub/simple/src/compiler/10.frontend/syntax_opt/README.md).

Current implementation lives in `src/compiler/10.frontend/desugar/` and covers:

- async desugaring
- placeholder lambda rewrite
- collection pattern desugaring
- related syntax-normalization analyses

### MIR optimization

Grouped under `src/compiler/60.mir_opt/`.

Current implemented passes include:

- constant folding
- copy propagation
- dead code elimination
- global value numbering
- common subexpression elimination
- inlining
- loop optimizations
- outlining
- SIMD lowering/vectorization-related passes

### Native executable optimization

Used by `simple compile --native`.

Current implemented native-path controls are:

- release build mode
- 4KB layout optimization
- strip / PIE / shared / map controls

## Levels

### `none`

- Native path: debug build mode
- Layout optimization: disabled

### `basic`

- Native path: release build mode
- Layout optimization: disabled

### `standard`

- Native path: release build mode
- Layout optimization: disabled

### `aggressive`

- Native path: release build mode
- Layout optimization: enabled
- This is the default profile for native executable builds

## Default

`simple compile --native` now defaults to the **aggressive** profile so executable builds use the strongest currently implemented native optimization set by default.

## Notes

- Syntax and MIR entries describe currently implemented optimization inventory across the compiler codebase.
- The Rust native executable path does not yet consume every self-hosted MIR optimization entry directly.
- The compile CLI can print the current inventory with `simple compile --list-optimizations`.
