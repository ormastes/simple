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
- Main implementation changed MIR pass descriptor lookup from rebuilding and
  scanning the descriptor registry on each lookup to direct exact dispatch for
  stable pass names and aliases.

## Remaining

1. Implement a shared MIR visitor/transform API.
2. Convert the remaining `run_pass_on_module` execution branch from pass-name
   string matching to a typed runner while preserving stable public pass names.
3. Design a versioned dynamic optimizer manifest.
4. Add native compile-time benchmark coverage for `pattern_idiom` on large MIR.
