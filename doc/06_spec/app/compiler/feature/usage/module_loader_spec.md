# Module Loader Specification

Tests the SMF module loader and registry including:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LOADER-001 to #LOADER-027 |
| Category | Runtime \| Module System |
| Status | Implemented |
| Source | `test/feature/usage/module_loader_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests the SMF module loader and registry including:
- SMF header validation
- Symbol table operations
- Relocation patching
- Module loading and caching
- Registry symbol resolution
- Section permissions
- Module reloading

## SMF Format

Simple Module Format (SMF) is the binary module format:
- Header with magic number, version, flags
- Section table (code, data, rodata, reloc)
- Symbol table with name hashing
- Relocations for linking

## Symbol Types

- `Function` - Callable code symbol
- `Data` - Mutable data symbol

## Symbol Bindings

- `Global` - Exported, visible to other modules
- `Local` - Internal, not exported

## Syntax

```simple
val module = loader.load("path/to/module.smf")

val func = module.get_function("entry")

val addr = registry.resolve_symbol("my_func")
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/module_loader/result.json` |

## Scenarios

- rejects bad magic number
- resolves symbol by name
- returns symbol name from offset
- patches local symbol address
- loads minimal module
- executable module has entry point
- code memory contains expected bytes
- caches loaded modules
- resolves exported symbol
- resolves imports via registry
- name_str returns trimmed name
- executable section has EXEC flag
- data section has WRITE flag
- rodata section is read-only
- section can have all flags
- get_function returns None for data symbol
- source_hash is readable
- entry_point returns None for non-executable
- get_function works on library modules
- exports lists global symbols
- is_reloadable checks flag
- get_fn finds existing function
- get_fn returns None for missing
- entry_fn returns entry point
- unload removes from cache
- unload returns false for uncached
- reload replaces cached module
- reload updates cache
- resolve returns None for unknown symbol
- resolve ignores local symbols
- load nonexistent fails
- unload nonexistent returns false
