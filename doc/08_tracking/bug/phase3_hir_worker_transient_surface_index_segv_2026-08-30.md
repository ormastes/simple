# Phase 3 HIR worker reads released surface-index dictionary

- Filed: 2026-08-30
- Severity: high
- Status: fixed in source; successor artifact blocked at runtime-provider link
- Exact reproducer compiler SHA-256: `323237d17a424b3f1e26185fd809765981d65b4f31e7288b0caa448e547788f2`

## Failure

The pure positional test-runner build discovers 177 modules and freezes 276
module surfaces, then every HIR worker dies before lowering the first module.
An isolated one-thread GDB reproduction removes scheduling and memory-pressure
variables and gives this stack:

1. `module_surface_registry_index`
2. `HirLowering.surface_index_for_name`
3. `HirLowering.resolve_import_symbols`
4. `HirLowering.lower_module`

The crash is therefore deterministic per worker, not a parallel race.

## Root cause and correction

`ModuleSurfacesByName.index_by_name` is a construction-time dictionary owned by
the transient surface arena. The arena is released after `surface_freeze`.
`module_surface_registry_index` attempted to detect the stale carrier by calling
`index_by_name.len()`, but that call itself dereferenced released storage.

The package lookup now uses only the promoted aligned scalar arrays. The HIR
lowerer lazily builds its own post-teardown scalar dictionary once, preserving
O(1) hot import lookup without touching the construction carrier. Regression
coverage poisons the compatibility dictionary and proves retained-array hits
and misses remain authoritative.

## Evidence

See `build/native_probe/phase3-worker-crash/receipt.md`. The fixed source passes
all 821 compiler modules through HIR and code generation. Candidate publication
is independently blocked at link because the selected `core-c-bootstrap` lane
does not link providers already present in the frozen capsule, including
`rt_native_build`, `rt_range`, and `rt_cranelift_*`.
