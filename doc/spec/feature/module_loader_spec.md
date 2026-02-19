# Module Loader Specification

**Feature ID:** #LOADER-001 to #LOADER-027 | **Category:** Runtime | Module System | **Status:** Implemented

_Source: `test/feature/usage/module_loader_spec.spl`_

---

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
# Load a module
val module = loader.load("path/to/module.smf")

# Get a function by name
val func = module.get_function("entry")

# Resolve symbol from registry
val addr = registry.resolve_symbol("my_func")
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 32 |

## Test Structure

### SMF Header Validation

- ✅ rejects bad magic number
### Symbol Table Operations

- ✅ resolves symbol by name
- ✅ returns symbol name from offset
### Relocation Patching

- ✅ patches local symbol address
### Module Loading

- ✅ loads minimal module
- ✅ executable module has entry point
- ✅ code memory contains expected bytes
### Module Registry

- ✅ caches loaded modules
- ✅ resolves exported symbol
- ✅ resolves imports via registry
### Section Properties

- ✅ name_str returns trimmed name
- ✅ executable section has EXEC flag
- ✅ data section has WRITE flag
- ✅ rodata section is read-only
- ✅ section can have all flags
### Module Methods

- ✅ get_function returns None for data symbol
- ✅ source_hash is readable
- ✅ entry_point returns None for non-executable
- ✅ get_function works on library modules
- ✅ exports lists global symbols
- ✅ is_reloadable checks flag
### DynModule Trait

- ✅ get_fn finds existing function
- ✅ get_fn returns None for missing
- ✅ entry_fn returns entry point
### Registry Unload and Reload

- ✅ unload removes from cache
- ✅ unload returns false for uncached
- ✅ reload replaces cached module
- ✅ reload updates cache
### Registry Error Handling

- ✅ resolve returns None for unknown symbol
- ✅ resolve ignores local symbols
- ✅ load nonexistent fails
- ✅ unload nonexistent returns false

