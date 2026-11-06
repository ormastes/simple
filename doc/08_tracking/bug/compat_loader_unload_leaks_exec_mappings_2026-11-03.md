# Compat loader unload() never frees executable mappings

Status: open

`ModuleLoader.unload` (src/compiler/99.loader/module_loader_compat.spl) drops
`global_symbols`/module entries but never calls `native_free_exec_memory` for
the module's code mappings or its GOT, so every load/unload (reload) cycle leaks
`native_exec_memory_count()` entries and bytes. Sibling of
compat_loader_partial_exec_mapping_rollback_2026-08-25 (load-failure path, fixed).

Fix sketch: record the per-load ledger (addr,size pairs, incl. GOT) on
LoadedModule and unmap it exactly once in unload, after pins/final-unpin allow it.
Acceptance: load+unload x N leaves native_exec_memory_count() and total unchanged.

## 2026-11-06 fixed (r11 mem lane)

`LoadedModule` now carries `exec_mappings: [i64]` (the load transaction's flat
`[addr, size, ...]` ledger, code + GOT) handed over at the commit point;
`ModuleLoader.unload` unmaps it exactly once via `_compat_release_exec_mappings`
on the single path that drops the module record (gate-blocked early returns keep
the module and its mappings). Aspect-pack SMFs are admitted non-executable, so
the V3 final-unpin dynlib release path never shares an address with this ledger.

Measured on the Windows seed (`D:/dev/wt/seed/simple.exe`), spec
`test/01_unit/compiler/loader/module_loader_unload_exec_mapping_release_spec.spl`
(clang x86_64-linux object -> SMF fixture, one code mapping of 11 bytes):

| | mappings after unload | bytes after unload | after 4 more cycles |
|---|---|---|---|
| before | baseline + 1 | baseline + 11 | baseline + 3 / + 33 (linear growth) |
| after | baseline | baseline | baseline |

Collateral: `module_loader_partial_mapping_rollback_spec`,
`aspect_final_unpin_v3_authority_spec`, `aspect_catalog_invalidation_spec`,
`module_loader_semantic_cache_spec`, `native_target_validation_spec` unchanged.
