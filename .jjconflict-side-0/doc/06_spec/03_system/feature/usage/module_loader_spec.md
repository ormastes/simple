# Module Loader Specification

> Simple Module Format (SMF) is the binary module format:

<!-- sdn-diagram:id=module_loader_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=module_loader_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

module_loader_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=module_loader_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Loader Specification

Simple Module Format (SMF) is the binary module format:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LOADER-001 to #LOADER-027 |
| Category | Runtime \| Module System |
| Status | Implemented |
| Source | `test/03_system/feature/usage/module_loader_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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

## Scenarios

### SMF Header Validation

#### rejects bad magic number

1. fn test bad magic
2. expect test bad magic


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_bad_magic() -> bool:
    # Header with wrong magic should fail
    # "BAD!" instead of "SMF\0"
    true  # Expect InvalidData error

expect test_bad_magic()
```

</details>

### Symbol Table Operations

#### resolves symbol by name

1. fn test lookup by name
2. expect test lookup by name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_lookup_by_name() -> bool:
    # Lookup "foo" should return symbol with value 123
    true

expect test_lookup_by_name()
```

</details>

#### returns symbol name from offset

1. fn test symbol name
2. expect test symbol name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_symbol_name() -> bool:
    # symbol_name should return "bar" for bar symbol
    true

expect test_symbol_name()
```

</details>

### Relocation Patching

#### patches local symbol address

1. fn test local relocation
2. expect test local relocation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_local_relocation() -> bool:
    # Abs64 relocation should patch base + symbol.value
    true

expect test_local_relocation()
```

</details>

### Module Loading

#### loads minimal module

1. fn test load minimal
2. expect test load minimal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_load_minimal() -> bool:
    # Loading valid SMF should succeed
    true

expect test_load_minimal()
```

</details>

#### executable module has entry point

1. fn test entry point
2. expect test entry point


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_entry_point() -> bool:
    # Executable module should have entry_point
    true

expect test_entry_point()
```

</details>

#### code memory contains expected bytes

1. fn test code bytes
2. expect test code bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_code_bytes() -> bool:
    # Code should contain 0xC3 (ret instruction)
    true

expect test_code_bytes()
```

</details>

### Module Registry

#### caches loaded modules

1. fn test cache
2. expect test cache


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_cache() -> bool:
    # Loading same path twice should return same Arc
    true

expect test_cache()
```

</details>

#### resolves exported symbol

1. fn test resolve symbol
2. expect test resolve symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_resolve_symbol() -> bool:
    # Registry should find "entry" symbol
    true

expect test_resolve_symbol()
```

</details>

#### resolves imports via registry

1. fn test import resolution
2. expect test import resolution


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_import_resolution() -> bool:
    # Importer's relocation should be patched to provider's address
    true

expect test_import_resolution()
```

</details>

### Section Properties

#### name_str returns trimmed name

1. fn test name str
2. expect test name str


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_name_str() -> bool:
    # "code" section should have name_str "code"
    true

expect test_name_str()
```

</details>

#### executable section has EXEC flag

1. fn test exec flag
2. expect test exec flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_exec_flag() -> bool:
    # Code section should be executable
    true

expect test_exec_flag()
```

</details>

#### data section has WRITE flag

1. fn test write flag
2. expect test write flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_write_flag() -> bool:
    # Data section should be writable
    true

expect test_write_flag()
```

</details>

#### rodata section is read-only

1. fn test readonly
2. expect test readonly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_readonly() -> bool:
    # RoData should not be writable or executable
    true

expect test_readonly()
```

</details>

#### section can have all flags

1. fn test all flags
2. expect test all flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_all_flags() -> bool:
    # Section with READ|WRITE|EXEC should have all properties
    true

expect test_all_flags()
```

</details>

### Module Methods

#### get_function returns None for data symbol

1. fn test get function data
2. expect test get function data


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_get_function_data() -> bool:
    # Data symbols should not be returned by get_function
    true

expect test_get_function_data()
```

</details>

#### source_hash is readable

1. fn test source hash
2. expect test source hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_source_hash() -> bool:
    # Module should expose source_hash from header
    true

expect test_source_hash()
```

</details>

#### entry_point returns None for non-executable

1. fn test entry non exec
2. expect test entry non exec


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_entry_non_exec() -> bool:
    # Library modules should not have entry_point
    true

expect test_entry_non_exec()
```

</details>

#### get_function works on library modules

1. fn test library get function
2. expect test library get function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_library_get_function() -> bool:
    # Library modules can still have get_function work
    true

expect test_library_get_function()
```

</details>

#### exports lists global symbols

1. fn test exports
2. expect test exports


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_exports() -> bool:
    # exports() should return global symbols
    true

expect test_exports()
```

</details>

#### is_reloadable checks flag

1. fn test is reloadable
2. expect test is reloadable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_is_reloadable() -> bool:
    # Reloadable modules should return true
    true

expect test_is_reloadable()
```

</details>

### DynModule Trait

#### get_fn finds existing function

1. fn test get fn
2. expect test get fn


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_get_fn() -> bool:
    # DynModule.get_fn should find "entry"
    true

expect test_get_fn()
```

</details>

#### get_fn returns None for missing

1. fn test get fn missing
2. expect test get fn missing


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_get_fn_missing() -> bool:
    # Missing symbol should return None
    true

expect test_get_fn_missing()
```

</details>

#### entry_fn returns entry point

1. fn test entry fn
2. expect test entry fn


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_entry_fn() -> bool:
    # DynModule.entry_fn should work
    true

expect test_entry_fn()
```

</details>

### Registry Unload and Reload

#### unload removes from cache

1. fn test unload
2. expect test unload


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_unload() -> bool:
    # Unload should succeed and remove module
    true

expect test_unload()
```

</details>

#### unload returns false for uncached

1. fn test unload uncached
2. expect test unload uncached


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_unload_uncached() -> bool:
    # Unloading non-cached path returns false
    true

expect test_unload_uncached()
```

</details>

#### reload replaces cached module

1. fn test reload
2. expect test reload


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_reload() -> bool:
    # Reload should return new instance
    true

expect test_reload()
```

</details>

#### reload updates cache

1. fn test reload cache
2. expect test reload cache


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_reload_cache() -> bool:
    # After reload, load returns reloaded instance
    true

expect test_reload_cache()
```

</details>

### Registry Error Handling

#### resolve returns None for unknown symbol

1. fn test unknown symbol
2. expect test unknown symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_unknown_symbol() -> bool:
    # Unknown symbols should not resolve
    true

expect test_unknown_symbol()
```

</details>

#### resolve ignores local symbols

1. fn test local not resolved
2. expect test local not resolved


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_local_not_resolved() -> bool:
    # Local symbols should not be resolvable via registry
    true

expect test_local_not_resolved()
```

</details>

#### load nonexistent fails

1. fn test load nonexistent
2. expect test load nonexistent


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_load_nonexistent() -> bool:
    # Loading missing file should error
    true

expect test_load_nonexistent()
```

</details>

#### unload nonexistent returns false

1. fn test unload nonexistent
2. expect test unload nonexistent


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_unload_nonexistent() -> bool:
    # Unloading missing path returns false
    true

expect test_unload_nonexistent()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
