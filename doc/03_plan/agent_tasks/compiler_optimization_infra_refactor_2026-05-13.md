# Compiler Optimization Infrastructure Refactor - Agent Tasks

Date: 2026-05-13

## Completed

- Repo mapping agent identified MIR optimization dispatch, pattern lookup, and
  plugin/dynamic loading boundaries.
- Domain research agent checked LLVM/MLIR pass and pattern infrastructure docs.
- Documentation agent mapped existing repo docs and confirmed built-in optimizer
  rules should precede dynamic loading for hot paths.
- Main implementation removed per-call-site cipher rule table reconstruction and
  added provider metadata for built-in vs dynamic optimizer rule sources.

## Remaining

1. Implement a shared MIR visitor/transform API.
2. Convert string pass dispatch to typed descriptors while preserving stable
   pass names.
3. Design a versioned dynamic optimizer manifest.
4. Add native compile-time benchmark coverage for `pattern_idiom` on large MIR.
