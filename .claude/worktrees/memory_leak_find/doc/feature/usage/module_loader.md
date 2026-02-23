# Module Loader Specification
*Source:* `test/feature/usage/module_loader_spec.spl`
**Feature IDs:** #LOADER-001 to #LOADER-027  |  **Category:** Runtime | Module System  |  **Status:** Implemented

## Overview



use std.text.{NL}

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
# Load a module
val module = loader.load("path/to/module.smf")

# Get a function by name
val func = module.get_function("entry")

# Resolve symbol from registry
val addr = registry.resolve_symbol("my_func")
```

## Feature: SMF Header Validation

## Magic Number and Format

    Tests SMF header parsing and validation.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | rejects bad magic number | pass |

**Example:** rejects bad magic number
    Then  expect test_bad_magic()

## Feature: Symbol Table Operations

## Symbol Resolution

    Tests symbol lookup by name and hash.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | resolves symbol by name | pass |
| 2 | returns symbol name from offset | pass |

**Example:** resolves symbol by name
    Then  expect test_lookup_by_name()

**Example:** returns symbol name from offset
    Then  expect test_symbol_name()

## Feature: Relocation Patching

## Code Patching

    Tests relocation application for linking.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | patches local symbol address | pass |

**Example:** patches local symbol address
    Then  expect test_local_relocation()

## Feature: Module Loading

## ModuleLoader Operations

    Tests loading SMF files into memory.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | loads minimal module | pass |
| 2 | executable module has entry point | pass |
| 3 | code memory contains expected bytes | pass |

**Example:** loads minimal module
    Then  expect test_load_minimal()

**Example:** executable module has entry point
    Then  expect test_entry_point()

**Example:** code memory contains expected bytes
    Then  expect test_code_bytes()

## Feature: Module Registry

## Caching and Resolution

    Tests registry caching and symbol resolution.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | caches loaded modules | pass |
| 2 | resolves exported symbol | pass |
| 3 | resolves imports via registry | pass |

**Example:** caches loaded modules
    Then  expect test_cache()

**Example:** resolves exported symbol
    Then  expect test_resolve_symbol()

**Example:** resolves imports via registry
    Then  expect test_import_resolution()

## Feature: Section Properties

## Section Flags and Names

    Tests section metadata access.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | name_str returns trimmed name | pass |
| 2 | executable section has EXEC flag | pass |
| 3 | data section has WRITE flag | pass |
| 4 | rodata section is read-only | pass |
| 5 | section can have all flags | pass |

**Example:** name_str returns trimmed name
    Then  expect test_name_str()

**Example:** executable section has EXEC flag
    Then  expect test_exec_flag()

**Example:** data section has WRITE flag
    Then  expect test_write_flag()

**Example:** rodata section is read-only
    Then  expect test_readonly()

**Example:** section can have all flags
    Then  expect test_all_flags()

## Feature: Module Methods

## Module API

    Tests Module struct methods.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | get_function returns None for data symbol | pass |
| 2 | source_hash is readable | pass |
| 3 | entry_point returns None for non-executable | pass |
| 4 | get_function works on library modules | pass |
| 5 | exports lists global symbols | pass |
| 6 | is_reloadable checks flag | pass |

**Example:** get_function returns None for data symbol
    Then  expect test_get_function_data()

**Example:** source_hash is readable
    Then  expect test_source_hash()

**Example:** entry_point returns None for non-executable
    Then  expect test_entry_non_exec()

**Example:** get_function works on library modules
    Then  expect test_library_get_function()

**Example:** exports lists global symbols
    Then  expect test_exports()

**Example:** is_reloadable checks flag
    Then  expect test_is_reloadable()

## Feature: DynModule Trait

## Trait Interface

    Tests DynModule trait implementation.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | get_fn finds existing function | pass |
| 2 | get_fn returns None for missing | pass |
| 3 | entry_fn returns entry point | pass |

**Example:** get_fn finds existing function
    Then  expect test_get_fn()

**Example:** get_fn returns None for missing
    Then  expect test_get_fn_missing()

**Example:** entry_fn returns entry point
    Then  expect test_entry_fn()

## Feature: Registry Unload and Reload

## Hot Reloading

    Tests module unloading and reloading.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | unload removes from cache | pass |
| 2 | unload returns false for uncached | pass |
| 3 | reload replaces cached module | pass |
| 4 | reload updates cache | pass |

**Example:** unload removes from cache
    Then  expect test_unload()

**Example:** unload returns false for uncached
    Then  expect test_unload_uncached()

**Example:** reload replaces cached module
    Then  expect test_reload()

**Example:** reload updates cache
    Then  expect test_reload_cache()

## Feature: Registry Error Handling

## Loading Failures

    Tests registry error cases.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | resolve returns None for unknown symbol | pass |
| 2 | resolve ignores local symbols | pass |
| 3 | load nonexistent fails | pass |
| 4 | unload nonexistent returns false | pass |

**Example:** resolve returns None for unknown symbol
    Then  expect test_unknown_symbol()

**Example:** resolve ignores local symbols
    Then  expect test_local_not_resolved()

**Example:** load nonexistent fails
    Then  expect test_load_nonexistent()

**Example:** unload nonexistent returns false
    Then  expect test_unload_nonexistent()


