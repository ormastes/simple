# Agent Task Breakdown — Loader Shared-Core Refactor

Feature: `FR-COMPILER-011`

## Scope

Refactor the compatibility loader and lifecycle-aware runtime loader so they
share the same core logic for unload/reload/JIT ownership handling without
breaking the pure-Simple compatibility harness.

Primary files:

- `src/compiler/99.loader/module_loader.spl`
- `src/compiler/99.loader/loader/module_loader.spl`
- `src/compiler/99.loader/jit_instantiator.spl`
- `src/compiler/99.loader/loader/jit_instantiator.spl`

Primary tests:

- `test/unit/compiler/loader/module_loader_spec.spl`
- `test/unit/compiler/loader/module_loader_crash_fix_spec.spl`

## Constraints

1. Do not start with a full file merge.
2. Do not treat method/exported-entrypoint delegation as automatically safe.
3. Keep `check-core-runtime-smoke` and `check-mcp-native-smoke` green.
4. Prefer sharing a narrow ownership-policy seam before broader reload/load
   unification.

## Work Split

### Track A — Shared Ownership Contract

- Write the exact invariants both loaders must satisfy:
  - unknown-path unload is a no-op
  - loaded-module unload removes metadata-owned JIT symbols
  - metadata beats heuristics when both exist
  - reload preserves post-reload resolvability for persisted JIT symbols
  - global-symbol rebuild is deterministic after unload
- Output:
  - update `doc/05_design/loader_shared_core_refactor.md`

### Track B — Shared Helper Extraction

- Extract the narrowest shared seam around metadata-backed JIT symbol names.
- First helper target:
  - `metadata_instantiation_symbol_names(metadata) -> [text]`
- This helper should only walk `metadata.instantiations[*].mangled_name`.
- Do not bundle broader unload policy into this first extraction.
- Keep the helper small enough that both loaders can adopt it without changing
  outer control flow or lifecycle ownership structure.
- Output:
  - shared helper module or helper surface under `src/compiler/99.loader/`

### Track C — Compatibility Loader Adoption

- Switch `src/compiler/99.loader/module_loader.spl` to the shared seam.
- Preserve current verified behavior:
  - unknown-path unload safety
  - metadata cleanup
  - metadata-owned JIT eviction
  - reload metadata rehydration
- Output:
  - compatibility loader uses shared ownership policy

### Track D — Lifecycle-Aware Loader Adoption

- Switch `src/compiler/99.loader/loader/module_loader.spl` to the same shared
  ownership seam or a provably equivalent wrapper.
- Ensure resource lifecycle logic remains intact.
- Output:
  - runtime loader uses same ownership policy

### Track E — Verification

- Add or tighten tests proving both loaders satisfy the same unload/reload
  invariants.
- Required verification:
  - `bin/simple test test/unit/compiler/loader/module_loader_spec.spl`
  - `bin/simple test test/unit/compiler/loader/module_loader_crash_fix_spec.spl`
  - runtime-loader-focused regression coverage for the lifecycle-aware path
  - `sh scripts/check-core-runtime-smoke.shs src/compiler_rust/target/release/simple`
  - `SIMPLE_BINARY=src/compiler_rust/target/release/simple sh scripts/check-mcp-native-smoke.shs`

## Recommended Order

1. Track A
2. Track B
3. Track C
4. Track D
5. Track E

## Stop Conditions

Stop and escalate instead of forcing the refactor if:

- the shared seam requires changing unrelated loader lifecycle architecture
- the compatibility harness still diverges when using the shared helper
- reload parity requires a broader state model redesign rather than a helper
  extraction
- the two JIT layers cannot share on the common metadata shape without a
  nominal-type bridge that is larger than the helper itself

## Current Remaining Work

Status after the 2026-04-27 shared-helper and lifecycle-coverage passes:

- Done:
  - feature request filed as `FR-COMPILER-011`
  - design seed written in `doc/05_design/loader_shared_core_refactor.md`
  - first shared seam landed:
    `src/compiler/99.loader/metadata_symbols.spl`
  - shared unload-bookkeeping helpers landed:
    `src/compiler/99.loader/unload_ownership.spl`
  - both loaders now consume the shared helper layer for:
    metadata-instantiation symbol names, loaded-metadata path removal,
    owned-global-symbol name collection, and global-symbol filtering by name
  - compatibility loader baseline restored on this branch
  - focused compatibility specs green
  - lifecycle-aware loader regression coverage added in
    `test/unit/compiler/loader/module_loader_spec.spl` proving unload removes
    path-owned globals, clears metadata-owned JIT symbols, preserves unrelated
    globals, and clears loaded metadata

- Still open for spawned-agent execution:
  1. Treat the current helper boundary as the default stop point unless a new
     candidate seam comes with explicit evidence that it does not cross either
     reload-policy or unload-ownership-policy differences.
  2. If broader sharing is attempted later, evaluate candidates in this order:
     reload orchestration, unload orchestration, tiny finalization helpers.
     Current recommendation is to reject the first two and skip the third as
     too small to justify the indirection.
  3. Separate but relevant repo health item: the SSH transport spec path still
     has pre-existing helper drift (`str.to_bytes()`), while
     `test/system/os_ssh_host_key_loader_spec.spl` remains green.

- Current stop boundary:
  - Do not extract any cross-loader helper that decides which JIT symbols to
    unload once that decision depends on compatibility heuristics
    (`_symbol_matches_path(...)`, exec-mapper owner probing) or full-loader
    lifecycle ownership state (`lifecycle_unload_module(...)`).
  - Shared refactor is currently safe only at the helper-level
    bookkeeping/data-selection seams already landed.
