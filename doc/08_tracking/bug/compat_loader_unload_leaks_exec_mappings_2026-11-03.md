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
