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

_(none — all items completed 2026-05-16)_

## Completed (continued 2026-05-16)

- Added `PassKind` enum (one variant per built-in pass) and `PassScope`
  (`Function` / `Module`) to `MirPassDescriptor`; both `mir_pass_descriptor()`
  constructor and `mir_pass_descriptor_for_name()` now carry typed kind+scope.
- Replaced string-match dispatch in `run_named_pass` and `run_pass_on_module`
  with typed runners: `run_typed_pass_on_function(kind, func)` and
  `run_typed_pass_on_module(kind, module)`.  Public pass names and aliases are
  unchanged.  Module-scope passes (`PatternIdiom`, `AutoVectorize`,
  `BodyOutlining`, inline variants, `PredicatePromote`) are explicitly routed
  to module-level runners; per-function no-ops removed.
- Implemented `MirVisitor` and `MirRewriter` shared traits in
  `mir_opt/mir_visitor.spl` with default walk helpers
  (`mir_visitor_walk_module/function/block/inst`) and rewriter application
  functions (`mir_rewriter_apply_to_function/block/module`).  Includes a
  `MirInstCounter` utility visitor.
- Designed versioned dynamic optimizer manifest: design doc at
  `doc/05_design/optimizer_manifest_versioned_design.md`; skeleton impl at
  `src/compiler/60.mir_opt/optimizer_manifest.spl` with `ManifestError`,
  `OptimizerManifest`, `DynamicPassRegistry`, `load_manifest_v1`, and
  conflict-guard helpers.
- Added `test/unit/compiler/mir/mir_pattern_idiom_benchmark_spec.spl` with
  synthetic large-MIR builders (100-function modules) and benchmark specs
  verifying `pattern_idiom` pass correctness, typed vs string dispatch
  consistency, `MirInstCounter` accuracy, and `PassScope` correctness for all
  built-in passes.
