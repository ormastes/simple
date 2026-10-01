# Retired bootstrap specs: module-surface ownership and Stage 4 streaming

- **Filed:** 2026-09-26
- **Status:** open — re-land the feature, then restore the retired examples from their origin commits
- **Component:** `src/compiler/20.hir/hir_lowering/module_surface*.spl`, `src/compiler/80.driver/driver_source_pipeline_*.spl`, runtime transient/discard arenas, CLI lint entry

## Why these were retired

These specs were rewritten or added by the share-history squash `e274cd33719`
(2026-08-27). They pin a streaming, owner-sliced module-surface design that
lived on side branches. `fcbec1c3b62` / `e9da588ee61` restored the source to the
origin lineage, which does not have that design. They failed on Windows
bootstrap46 under the delegated seed.

Owner decision 2026-09-26: every example whose behaviour exists on main was
retargeted with a cited commit; only the examples below were retired. Whole-file
deletions: `entry_closure_module_map_update_spec.spl`.

## Missing features

| Spec (test/01_unit/compiler/bootstrap/) | Retired example(s) | Missing on main | Origin commit |
|---|---|---|---|
| `module_surface_callable_projection_contract_spec.spl` | "retains callable payloads as reference-semantic classes"; "keeps the current reference-semantic callable lookup coherent"; "projects composite fields without reopening retained payload dictionaries"; the generic array-element branch of "projects imported aggregate types…" | Reference-semantic `ModuleSurfaceCallable` with index-aligned callable payloads; composite projection through `field_offsets` / `dependency_names`; the generic `imported_surface_type` array-element branch | `8e088e40ddf` (branch-only, 2026-08-22) |
| same | "uses frozen scalar routes for cross-stage import traversal"; "…for primary import registration"; "shares one glob memo across a package sibling expansion" | Frozen scalar import routes (`import_route_module_names` / `import_route_item_offsets` / `import_route_item_local_names`); one package-level glob memo shared across sibling expansions (main resets `glob_expand_memo`) | `8e088e40ddf` |
| `module_surface_canonical_once_spec.spl` | HIR-phase physical-surface lookup part; batch owner-builder part; "keeps path-taking owner wrappers without whole parser modules" | Phase-3 lookup by physical identity; `module_surfaces_from_owners` + `add_parsed_or_alias(owner: ModuleSurfaceParserOwner)`; builder methods that take owners, not whole `ParserModule`s | `7f173fd9b87` (branch-only, 2026-08-05) |
| `stage4_streaming_surfaces_contract_spec.spl` | sliced-owner part of "bounds source 11…"; "keeps the global export owner index out of native text dictionaries"; "reclaims Stage3 closure import scanner scratch per source"; "prepares persistent frontend owners before both streaming phases"; discard-arena parts of "builds the retained surface…" and "walks retained graphs…"; released-log part of "reclaims each reparsed AST…"; slot-metadata part of "promotes only new aggregate tails…" | `ModuleSurfaceParserOwner` holding only sliced fields; scalar `ModuleSurfaceOwnerIndex`; per-source transient scope around the Stage 3 closure scan; `frontend_prepare_transient_parse_scope()` before both phases; `rt_transient_discard_scope_begin` discard-only arena with raw-alloc table release/trim; `log_hir_transient_scope_released`; `[i64]` slot transaction metadata | `522f32ed05d` (branch-only, 2026-08-21) |
| `entry_closure_module_map_update_spec.spl` | whole file | `driver_source_pipeline_parsing.spl` still retains parsed modules through `ParsedEntryModuleBox` / `parsed_box.value` / `add_parsed`; owner-backed surfaces are not prebuilt on every parse branch | `e274cd33719` (no source-branch commit survives) |
| `entry_closure_physical_source_dedup_spec.spl` | "loads relative mod declarations in the pure driver closure" | The pure driver closure ignores sibling `mod` / export-member paths from `_driver_cached_entry_source_scan`; only the native-build closure follows them | `e274cd33719` |
| `lint_short_grammar_helper_import_contract_spec.spl` | "keeps full-cli lint helpers at concrete lazy owners" | CLI lint/run lazily import `check_simd_opportunities` / `check_short_grammar_refactor` through the `compiler.tools.fix.rules` facade, not from the concrete `rules.impl_` owners | `e274cd33719` |

## Re-land checklist

1. Land the design slice on main.
2. `git show <origin>:test/01_unit/compiler/bootstrap/<spec>` and restore the
   retired example. Escape literal `{` in needles as `\{`.
3. Run it under the seed and the self-hosted CLI; it must pass on both.
