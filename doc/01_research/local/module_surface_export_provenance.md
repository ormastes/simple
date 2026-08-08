<!-- codex-research -->
# Module Surface Export Provenance — Local Research

## Trigger

Stage 4 emitted 1,713 HIR diagnostics across 234 files. Only 108 exact messages
and 539 file/message pairs existed; repeated occurrences accounted for 68.5%.
Missing `Symbol` and `Span` types alone produced 972 diagnostics in 51 driver
files. This is characteristic of a shared module-surface/re-export failure with
large downstream fan-out, not 1,713 independent defects.

## Current ownership and flow

- `src/compiler/20.hir/hir_lowering/module_surface.spl` owns
  `ModuleSurface`, `ModuleSurfacesByName`, and `ModuleSurfaceBuilder`.
  Surfaces retain canonical physical identity, fingerprints, raw
  `ParserImport`/`Export`, and direct declaration dictionaries.
- `ModuleSurfaceBuilder.add_parsed` admits one physical source;
  `add_alias` maps logical spellings to the existing surface index.
- `src/compiler/80.driver/driver_source_loading.spl` generates entry-closure
  aliases in `_driver_module_aliases`, including numbered-tier normalization,
  `compiler.core.*`, and conditional `std.*` spellings.
- `driver_source_pipeline_parsing.spl::parse_all_streaming_surfaces_impl`
  builds compact surfaces. Retained paths rebuild them in
  `driver_hir_pipeline_lowering.spl` and `compile_c_entry.spl`.
- `_Items/module_lowering.spl::resolve_module_key[_relative]` tries literal,
  `.__init__`, `lib.*`, `std`-to-`lib`, and runtime-family spellings.
- `find_reexport_source` repeatedly interprets raw imports/exports for each
  requested name, stops at depth eight, and does not retain provenance.
  `register_glob_imported_symbols_depth` implements a second export traversal.

## Existing evidence

- `test/01_unit/compiler/hir/module_surface_spec.spl`: physical aliases and
  declaration-shape ambiguity.
- `test/01_unit/compiler/hir/resolve_import_symbols_spec.spl`: direct, glob,
  named, and aliased compatibility re-exports.
- `test/01_unit/compiler/driver/driver_source_loading_spec.spl` and
  `bootstrap/entry_closure_physical_source_dedup_spec.spl`: alias generation.
- `bootstrap/stage4_streaming_surfaces_contract_spec.spl`: compact surface
  retention contract.

## Gap and immediate safe slice

The surface knows where a module came from but not where an exported name was
declared. A compact precomputed re-export-origin map can unify explicit and glob
resolution without duplicating direct declarations. Build it only after all
surfaces and aliases exist; key owners by surface index/canonical path, never by
the import spelling. Keep the old chase as temporary diagnostic fallback.

## Future boundary

The immediate map is not the final dependency model. A later
`ResolvedModuleGraph` should own canonical module nodes, typed import/export
edges, visibility, cycles, and symbol-body closure. Entry closure and HIR should
then consume the same resolved graph rather than reconstructing reachability.

Sidecars: N/A for this documentation lane. Final review: normal/highest-capability
merge owner.
