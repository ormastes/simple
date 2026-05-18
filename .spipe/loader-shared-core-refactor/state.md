# SStack State: loader-shared-core-refactor

## User Request
> next task from the plan — loader_shared_core_refactor (5 tracks: shared seam extraction, invariant definition, compatibility loader adoption, runtime loader adoption, verification)

## Task Type
feature

## Refined Goal
> Formalize loader shared-core unload/reload policy: define invariant contract type, verify both loaders (compatibility + runtime) satisfy the same unload/reload/JIT-ownership invariants via the existing shared helpers (metadata_symbols, unload_ownership), and add verification specs.

## Acceptance Criteria
- [ ] AC-1: Shared unload policy — UnloadPolicy with metadata-first + heuristic-fallback ordering, symbol collection, global rebuild
- [ ] AC-2: Unload invariant contract — InvariantCheck with unknown-path-noop, metadata-cleanup, heuristic-fallback, reload-resolvability, deterministic-rebuild
- [ ] AC-3: Metadata symbol extraction — shared helper surface for metadata_instantiation_symbol_names with path-keyed lookup
- [ ] AC-4: Global symbol ownership — shared helper surface for owned_global_symbol_names + global_symbols_without_names
- [ ] AC-5: Unload invariant: unknown-path unload is no-op (no symbols removed, no state change)
- [ ] AC-6: Unload invariant: loaded-module unload removes metadata-owned JIT symbols
- [ ] AC-7: Unload invariant: metadata beats heuristics when both exist for the same symbol
- [ ] AC-8: Reload invariant: persisted JIT symbols remain resolvable after reload
- [ ] AC-9: Rebuild invariant: global-symbol table is deterministic after unload+rebuild
- [ ] AC-10: Verification spec — 20 tests covering policy, invariants, metadata, ownership, unload/reload

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [x] 2-4 — skipped (plan doc comprehensive)
- [x] 5-implement (Engineer) — 2026-05-18
- [x] 6-refactor (Tech Lead) — 2026-05-18
- [x] 7-verify (QA) — 2026-05-18
- [x] 8-ship (Release Mgr) — 2026-05-18

## Phase Outputs

### 1-dev
10 ACs across 5 plan tracks (A-E). Existing shared helpers: metadata_symbols.spl (loaded_metadata_instantiation_symbol_names, loaded_metadata_remove_path), unload_ownership.spl (owned_global_symbol_names, global_symbols_without_names). Both loaders already import these. Task: formalize invariant contract + verification.

### 5-implement
5 parallel Sonnet agents. 5 files created:
- src/compiler/99.loader/unload_policy.spl — UnloadPolicy + GlobalRebuildResult + InvariantCheck + InvariantReport
- src/compiler/99.loader/metadata_symbol_surface.spl — MetadataSymbolEntry + MetadataSymbolIndex + GlobalSymbolOwnership + OwnershipTransfer
- src/compiler/99.loader/unload_scenario.spl — UnloadScenario + UnloadResult + ReloadScenario + ScenarioVerdict
- src/compiler/99.loader/reload_rebuild.spl — JitSymbolState + ReloadResolvability + GlobalTableSnapshot + DeterminismCheck + RebuildReport
- test/unit/compiler/loader/loader_shared_core_spec.spl — 20 tests

### 7-verify
20/20 tests PASS.
