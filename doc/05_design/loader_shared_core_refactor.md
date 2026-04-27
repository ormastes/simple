# Loader Shared-Core Refactor Seed

Feature: `FR-COMPILER-011`

## Goal

Reduce semantic drift between:

- `src/compiler/99.loader/module_loader.spl`
- `src/compiler/99.loader/loader/module_loader.spl`

The immediate target is not “make the files look similar”. The target is to
make the compatibility loader and the lifecycle-aware loader share the same
state-transition rules for:

- module load / reload / unload
- JIT cache ownership
- metadata hydration and cleanup
- global symbol rebuild after unload

## Why This Exists

The 2026-04-27 stabilization session found multiple real behavior gaps in the
compatibility loader that the lifecycle-aware loader did not share:

1. unknown-path unload could evict unrelated heuristic-matching JIT symbols
2. unload of a loaded module could leave `jit.loaded_metadata[path]` behind
3. unload could miss metadata-owned JIT symbols when cached owner state drifted
4. reload could clear metadata and fail to rehydrate persisted JIT capability

Those fixes were all narrow and verified, but they showed that the two loaders
are parallel implementations with overlapping semantics rather than a single
shared behavior core.

## Non-Goal

Do not start by merging the two files wholesale.

The compatibility loader runs in a stricter pure-Simple harness, and a seemingly
safe delegation change:

- `ModuleLoader.unload(...) -> moduleloader_unload(...)`

was not behaviorally equivalent there. That means the first refactor step must
be a carefully chosen shared seam, not a blanket deduplication pass.

## Recommended Refactor Shape

### Phase 1: Shared behavior contract

Write down exact invariants for both loaders:

1. unknown-path unload is a no-op
2. unloading a loaded module removes all JIT symbols owned by that module
3. authoritative ownership metadata wins over name/path heuristics
4. unloading a loaded module removes loader-visible metadata for that path
5. reload preserves post-reload resolvability for persisted JIT/generic symbols
6. rebuild of `global_symbols` after unload is deterministic and ownership-aware

This can live either in this doc or a follow-on architecture note.

#### First invariants to prove in code

The first implementation slice should prove only these invariants, because they
are already semantically aligned enough across both loaders:

1. `LoadedMetadata.instantiations[*].mangled_name` is an authoritative list of
   module-originated JIT symbol names.
2. Both loaders may derive unload candidates from that metadata list before
   consulting broader ownership policy.
3. Shared extraction must stop at “metadata says these symbol names belong to
   the module”; it must not yet unify the broader question of which pages,
   cache records, mapper entries, or lifecycle resources to free.

This keeps the first seam data-oriented and avoids collapsing the
compatibility-loader heuristics into the lifecycle-aware ownership model.

### Phase 2: Extract the first shared seam

Prefer a helper/module boundary around unload ownership collection rather than
full loader unification.

Candidate shared seam:

- extract `LoadedMetadata.instantiations[*].mangled_name` into a shared helper
  that both loaders use
- keep cache/exec-mapper ownership and heuristic fallback outside the first
  shared seam

This seam is narrow, high-value, and directly tied to the bugs already fixed.
It also avoids the failed “delegate the whole unload body” experiment that the
pure-Simple compatibility harness did not preserve behavior for.

### Phase 3: Share reload metadata policy

Both surfaces should agree on:

- when metadata is hydrated on load
- what reload is allowed to clear
- what persisted metadata must restore after reload

The compatibility loader currently rehydrates from sidecar metadata on load.
The runtime loader has a richer lifecycle path. The refactor should define one
policy and one proof shape even if the storage mechanism remains different.

## Verification Requirements

Minimum gates for any implementation pass:

- `bin/simple test test/unit/compiler/loader/module_loader_spec.spl`
- `bin/simple test test/unit/compiler/loader/module_loader_crash_fix_spec.spl`
- runtime-loader-focused regression coverage for the lifecycle-aware path
- `sh scripts/check-core-runtime-smoke.shs src/compiler_rust/target/release/simple`
- `SIMPLE_BINARY=src/compiler_rust/target/release/simple sh scripts/check-mcp-native-smoke.shs`

## First Concrete Implementation Slice

Recommended first slice for an implementation task:

1. introduce a shared helper surface for “module-owned JIT symbol collection”
2. migrate compatibility unload to that helper
3. migrate lifecycle-aware unload to the same helper or mirrored contract
4. prove identical unload outcomes on:
   - unknown-path unload
   - loaded-module unload with metadata
   - owner-drifted `__jit__` cache entries
   - reload after persisted JIT sidecar state

This is small enough to verify and large enough to prevent the exact drift that
already happened.

## Execution Plan

Task breakdown lives in:

- `doc/03_plan/agent_tasks/loader_shared_core_refactor.md`
