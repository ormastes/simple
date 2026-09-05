# Stage 4 promotes unused implementation metadata graphs

## Status and claim

FIXED — claimed by `stage4_perf_sol_high` on 2026-08-02. The change is scoped
to `src/compiler/20.hir/hir_lowering/module_surface.spl`; the concurrent
Stage-4 correctness lane owns driver/import repairs.

## Profile evidence

Stage 4 remains single-core through its dominant parse/surface and streaming
HIR work. The retained external sampler shows approximately 100% CPU for the
compiler process. A legacy Phase-2 trace completed 1,197 files in 148.5 seconds
while `heap_registry` grew to 49,245,805 objects. The latest completed
`82d440f8149` fail-fast cycle (PID 606749) reached 6,772,408 KiB RSS after 150
seconds and stopped in Phase 3 at 180 seconds on unrelated HIR errors. An older
pre-fail-fast diagnostic run (PID 2325544) continued on one core to 16,409,076
KiB RSS at 1,203 seconds; it is historical runaway evidence, not the current
acceptance run.

The interrupted profiler proposal to replace the whole implementation surface
with only `impl_count` was not valid on current main. Exhaustive owned-source
reference inspection found a real Phase-3 reader:
`register_imported_type_methods` scans `imported_mod.impls` and needs `type_`,
`has_trait_`, `trait_`, and `methods`. Removing those fields would break
imported inherent and trait method registration.

The same reference audit found no `ModuleSurfaceImpl` reader for `type_params`,
`where_clause`, `assoc_types`, or `span`. Ordinary HIR lowering reads those
fields from the per-file parser `Impl`, not from the promoted surface. Current
Stage-4 roots contain 3,964 syntactic implementation blocks (the interrupted
91a0789 snapshot contained 3,930). Before this fix each promoted record carried
eight fields; afterward it carries the four fields Phase 3 reads. This removes
15,856 dead promoted field edges across the current corpus, plus the reachable
generic-bound, associated-type, and span subgraphs behind those edges. This is
a static retained-graph measurement, not a claim that the multi-GiB parser
registry growth is solved.

## Repair

Keep `[ModuleSurfaceImpl]`, its exact length, and the four fields needed for
imported-method registration. Remove only the four proven-unused fields from
the promoted representation and converter. Alias declaration matching still
compares exact implementation counts.

## Verification

- `module_surface_impl_retention_spec.spl`: 2 examples, 0 failures.
- `resolve_import_symbols_spec.spl`: 22 examples, 0 failures, including equal
  implementation-count alias deduplication and adjacent unequal-count rejection.
- Optimizer O3 analysis completed for every touched `.spl` file. The new
  retention contract reported no opportunities; existing source/test findings
  were generic bounds-check, DCE, loop-hoist, and preallocation suggestions,
  with no contradiction to this data-layout fix.
- Direct environment runtime guards passed for working and staged trees.
- `simple check src/compiler` could not complete in this isolated worktree:
  spawned checks hard-code missing `bin/simple` and reported `exec:
  bin/simple: not found`. The focused interpreter suites above compiled and
  executed the changed paths.
- Adjacent `alias_static_call_resolution_spec.spl` is red 2/2 with generic
  `assert_true(false)` failures on both this candidate and untouched current
  main `03253b5a972`; it is a confirmed pre-existing failure, not a regression.

No candidate Stage-4 build was run: the final correctness cycle is the single
authorized Stage-4 cycle, and its compiler does not yet contain this fix. A
future generation comparison must not attribute that external cycle's RSS to
this change.
