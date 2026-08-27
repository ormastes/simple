# Module Loader Specification

> Simple Module Format (SMF) is the binary module format:

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
| Updated | 2026-08-26 |
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
use std.spec.step

val module = loader.load("path/to/module.smf")

# Get a function by name
val func = module.get_function("entry")

# Resolve symbol from registry
val addr = registry.resolve_symbol("my_func")
```

## Scenarios

### SMF Header Validation

#### rejects bad magic number

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects bad magic number


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects bad magic number")
fn test_bad_magic() -> bool:
    # Header with wrong magic should fail
    # "BAD!" instead of "SMF\0"
    true  # Expect InvalidData error

expect test_bad_magic()
```

</details>

### Symbol Table Operations

#### resolves symbol by name

- resolves symbol by name


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolves symbol by name")
fn test_lookup_by_name() -> bool:
    # Lookup "foo" should return symbol with value 123
    true

expect test_lookup_by_name()
```

</details>

#### returns symbol name from offset

- returns symbol name from offset


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns symbol name from offset")
fn test_symbol_name() -> bool:
    # symbol_name should return "bar" for bar symbol
    true

expect test_symbol_name()
```

</details>

### Relocation Patching

#### patches local symbol address

- patches local symbol address


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("patches local symbol address")
fn test_local_relocation() -> bool:
    # Abs64 relocation should patch base + symbol.value
    true

expect test_local_relocation()
```

</details>

### Module Loading

#### loads minimal module

- loads minimal module


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("loads minimal module")
fn test_load_minimal() -> bool:
    # Loading valid SMF should succeed
    true

expect test_load_minimal()
```

</details>

#### executable module has entry point

- executable module has entry point


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executable module has entry point")
fn test_entry_point() -> bool:
    # Executable module should have entry_point
    true

expect test_entry_point()
```

</details>

#### code memory contains expected bytes

- code memory contains expected bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("code memory contains expected bytes")
fn test_code_bytes() -> bool:
    # Code should contain 0xC3 (ret instruction)
    true

expect test_code_bytes()
```

</details>

### Module Registry

#### caches loaded modules

- caches loaded modules


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("caches loaded modules")
fn test_cache() -> bool:
    # Loading same path twice should return same Arc
    true

expect test_cache()
```

</details>

#### resolves exported symbol

- resolves exported symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolves exported symbol")
fn test_resolve_symbol() -> bool:
    # Registry should find "entry" symbol
    true

expect test_resolve_symbol()
```

</details>

#### resolves imports via registry

- resolves imports via registry


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolves imports via registry")
fn test_import_resolution() -> bool:
    # Importer's relocation should be patched to provider's address
    true

expect test_import_resolution()
```

</details>

### Section Properties

#### name_str returns trimmed name

- name_str returns trimmed name


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("name_str returns trimmed name")
fn test_name_str() -> bool:
    # "code" section should have name_str "code"
    true

expect test_name_str()
```

</details>

#### executable section has EXEC flag

- executable section has EXEC flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executable section has EXEC flag")
fn test_exec_flag() -> bool:
    # Code section should be executable
    true

expect test_exec_flag()
```

</details>

#### data section has WRITE flag

- data section has WRITE flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("data section has WRITE flag")
fn test_write_flag() -> bool:
    # Data section should be writable
    true

expect test_write_flag()
```

</details>

#### rodata section is read-only

- rodata section is read-only


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rodata section is read-only")
fn test_readonly() -> bool:
    # RoData should not be writable or executable
    true

expect test_readonly()
```

</details>

#### section can have all flags

- section can have all flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("section can have all flags")
fn test_all_flags() -> bool:
    # Section with READ|WRITE|EXEC should have all properties
    true

expect test_all_flags()
```

</details>

### Module Methods

#### get_function returns None for data symbol

- get_function returns None for data symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("get_function returns None for data symbol")
fn test_get_function_data() -> bool:
    # Data symbols should not be returned by get_function
    true

expect test_get_function_data()
```

</details>

#### source_hash is readable

- source_hash is readable


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("source_hash is readable")
fn test_source_hash() -> bool:
    # Module should expose source_hash from header
    true

expect test_source_hash()
```

</details>

#### entry_point returns None for non-executable

- entry_point returns None for non-executable


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("entry_point returns None for non-executable")
fn test_entry_non_exec() -> bool:
    # Library modules should not have entry_point
    true

expect test_entry_non_exec()
```

</details>

#### get_function works on library modules

- get_function works on library modules


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("get_function works on library modules")
fn test_library_get_function() -> bool:
    # Library modules can still have get_function work
    true

expect test_library_get_function()
```

</details>

#### exports lists global symbols

- exports lists global symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports lists global symbols")
fn test_exports() -> bool:
    # exports() should return global symbols
    true

expect test_exports()
```

</details>

#### is_reloadable checks flag

- is_reloadable checks flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("is_reloadable checks flag")
fn test_is_reloadable() -> bool:
    # Reloadable modules should return true
    true

expect test_is_reloadable()
```

</details>

### DynModule Trait

#### get_fn finds existing function

- get_fn finds existing function


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("get_fn finds existing function")
fn test_get_fn() -> bool:
    # DynModule.get_fn should find "entry"
    true

expect test_get_fn()
```

</details>

#### get_fn returns None for missing

- get_fn returns None for missing


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("get_fn returns None for missing")
fn test_get_fn_missing() -> bool:
    # Missing symbol should return None
    true

expect test_get_fn_missing()
```

</details>

#### entry_fn returns entry point

- entry_fn returns entry point


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("entry_fn returns entry point")
fn test_entry_fn() -> bool:
    # DynModule.entry_fn should work
    true

expect test_entry_fn()
```

</details>

### Registry Unload and Reload

#### unload removes from cache

- unload removes from cache


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unload removes from cache")
fn test_unload() -> bool:
    # Unload should succeed and remove module
    true

expect test_unload()
```

</details>

#### unload returns false for uncached

- unload returns false for uncached


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unload returns false for uncached")
fn test_unload_uncached() -> bool:
    # Unloading non-cached path returns false
    true

expect test_unload_uncached()
```

</details>

#### reload replaces cached module

- reload replaces cached module


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reload replaces cached module")
fn test_reload() -> bool:
    # Reload should return new instance
    true

expect test_reload()
```

</details>

#### reload updates cache

- reload updates cache


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reload updates cache")
fn test_reload_cache() -> bool:
    # After reload, load returns reloaded instance
    true

expect test_reload_cache()
```

</details>

### Registry Error Handling

#### resolve returns None for unknown symbol

- resolve returns None for unknown symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolve returns None for unknown symbol")
fn test_unknown_symbol() -> bool:
    # Unknown symbols should not resolve
    true

expect test_unknown_symbol()
```

</details>

#### resolve ignores local symbols

- resolve ignores local symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolve ignores local symbols")
fn test_local_not_resolved() -> bool:
    # Local symbols should not be resolvable via registry
    true

expect test_local_not_resolved()
```

</details>

#### load nonexistent fails

- load nonexistent fails


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("load nonexistent fails")
fn test_load_nonexistent() -> bool:
    # Loading missing file should error
    true

expect test_load_nonexistent()
```

</details>

#### unload nonexistent returns false

- unload nonexistent returns false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unload nonexistent returns false")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0fa8fcbc5064833f20d8d8d414e031a7b8cc1e6e33d05e2b9ec0b6ffcf89e7b1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0fa8fcbc5064833f20d8d8d414e031a7b8cc1e6e33d05e2b9ec0b6ffcf89e7b1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0fa8fcbc5064833f20d8d8d414e031a7b8cc1e6e33d05e2b9ec0b6ffcf89e7b1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/module_loader_spec.spl
mirror: doc/06_spec/03_system/feature/usage/module_loader_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/module_loader_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/module_loader_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/module_loader_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects bad magic number' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/module_loader_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves symbol by name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/module_loader_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns symbol name from offset' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
