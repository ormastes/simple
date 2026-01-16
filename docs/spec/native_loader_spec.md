# Native Loader (FFI & Dynamic Loading)

*Source: `simple/std_lib/test/features/infrastructure/native_loader_spec.spl`*

---

# Native Loader (FFI & Dynamic Loading)

**Feature ID:** #105
**Category:** Infrastructure - FFI
**Difficulty:** 3/5
**Status:** Complete

## Overview

The Native Loader provides Foreign Function Interface (FFI) capabilities, enabling
Simple programs to load and call functions from native dynamic libraries (.so/.dylib/.dll).
This infrastructure supports interoperability with C libraries, system APIs, and
existing native code.

Key components:
- **ModuleLoader:** Loads native dynamic libraries using libloading
- **LoadedModule:** Represents loaded library with symbol lookup
- **ModuleRegistry:** Centralized registry for loaded modules
- **RuntimeSymbolProvider:** Three-tier symbol resolution (static/dynamic/chained)
- **ABI Versioning:** Ensures runtime compatibility

## Key Features

- **Cross-Platform Loading:** Supports .so (Linux), .dylib (macOS), .dll (Windows)
- **Symbol Lookup:** Type-safe function pointer resolution
- **Module Registry:** Prevents duplicate loading, enables hot reload
- **Symbol Providers:** Static, dynamic, and chained resolution strategies
- **ABI Compatibility:** Version checking for runtime/module compatibility
- **Module Caching:** Reuses loaded libraries across calls

## Syntax

**Loading Native Libraries:**
```simple
# Load dynamic library
val lib = ModuleLoader.load("path/to/library.so")

# Lookup symbol
val add_fn = lib.get_fn<fn(i64, i64) -> i64>("add")

# Call native function
val result = add_fn(40, 2)  # 42
```

**Symbol Providers:**
```simple
# Static provider (compile-time linked)
val provider = static_provider()

# Dynamic provider (runtime resolved)
val provider = dynamic_provider("libruntime.so")

# Chained provider (fallback chain)
val provider = chained_provider([static, dynamic])
```

## Implementation

**Primary Files:**
- `src/native_loader/src/loader.rs` - ModuleLoader implementation
- `src/native_loader/src/module.rs` - LoadedModule wrapper
- `src/native_loader/src/registry.rs` - Module registry
- `src/native_loader/src/static_provider.rs` - Static symbol provider
- `src/native_loader/src/dynamic_provider.rs` - Dynamic symbol provider
- `src/native_loader/src/chained_provider.rs` - Chained provider

**Testing:**
- `src/native_loader/tests/native_loader_tests.rs` - FFI test suite (229 lines)

**Dependencies:**
- `libloading` crate for dynamic library loading
- Feature #103: Common Utilities (module cache, runtime symbols)

**Required By:**
- Feature #106: Driver (JIT compilation, native execution)
- Feature #7: RuntimeValue (FFI integration)

## Module Loading

### Dynamic Library Loading

**Platform Support:**
```
Linux:   .so files (ELF shared objects)
macOS:   .dylib files (Mach-O dynamic libraries)
Windows: .dll files (PE dynamic link libraries)
```

**Loading Process:**
```
1. Locate library file
2. Load into process memory (dlopen/LoadLibrary)
3. Resolve symbols (dlsym/GetProcAddress)
4. Return LoadedModule handle
5. Cache in registry
```

### Symbol Lookup

**Type-Safe Resolution:**
```simple
# Function pointer with signature
val sqrt_fn = lib.get_fn<fn(f64) -> f64>("sqrt")

# Verify type matches library signature
val result = sqrt_fn(42.0)  # Type-checked at compile time
```

**Symbol Resolution:**
```
1. Convert symbol name to C string
2. Look up in library symbol table
3. Cast to requested function pointer type
4. Return typed function pointer
```

## Runtime Symbol Providers

### Static Provider

Links symbols at compile time:
```rust
StaticSymbolProvider {
    symbols: {
        "malloc": malloc_impl,
        "free": free_impl,
        "print": print_impl,
    }
}
```

**Advantages:** Fast (no runtime lookup), guaranteed availability
**Disadvantages:** Fixed at compile time, larger binary

### Dynamic Provider

Resolves symbols from dynamic library:
```rust
DynamicSymbolProvider {
    library: Library::new("libruntime.so"),
}
```

**Advantages:** Flexible, smaller binary, hot reload
**Disadvantages:** Slower lookup, runtime dependency

### Chained Provider

Tries multiple providers in order:
```rust
ChainedProvider {
    providers: [static, dynamic, fallback]
}
```

**Resolution Strategy:** First match wins

## ABI Versioning

### Version Format

```rust
struct AbiVersion {
    major: u16,  # Breaking changes
    minor: u16,  # Compatible additions
    patch: u16,  # Bug fixes
}
```

### Compatibility Rules

- **Major:** Must match exactly (1.x.x ≠ 2.x.x)
- **Minor:** Backward compatible (1.2.x works with 1.3.x)
- **Patch:** Always compatible (1.2.3 works with 1.2.4)

### Version Checking

```simple
val provider = dynamic_provider("libruntime.so")
match provider.check_abi_version(1, 2, 0):
    Ok(_) => # Compatible, proceed
    Err(IncompatibleAbi) => # Abort, version mismatch
```

## Module Registry

### Registry Functions

**Insert:**
```simple
val registry = ModuleRegistry.new()
registry.insert("math.so", module)
```

**Lookup:**
```simple
match registry.get("math.so"):
    Some(module) => use_module(module)
    None => load_and_cache()
```

**Remove (Hot Reload):**
```simple
registry.remove("math.so")  # Unload old version
val new_module = loader.load("math.so")
registry.insert("math.so", new_module)
```

## Performance Characteristics

| Operation | Complexity | Notes |
|-----------|------------|-------|
| Library load | O(1) + dlopen | System call overhead |
| Symbol lookup | O(log n) | Binary search in symbol table |
| Registry lookup | O(1) | HashMap access |
| Static provider lookup | O(1) | Direct function pointer |
| Dynamic provider lookup | O(log n) | dlsym call |
| Chained provider lookup | O(k × log n) | k = provider count |

## Related Features

- Feature #103: Common Utilities (runtime symbols)
- Feature #106: Driver (native execution)
- Feature #7: RuntimeValue (FFI calls)

## Language Design Notes

**Safety vs Performance:**
Simple balances FFI safety with performance:
- Type-checked function signatures at call sites
- Unsafe loading (dlopen) encapsulated in safe API
- Runtime ABI checks prevent version mismatches

**Symbol Resolution Strategy:**
Chained providers enable flexible deployment:
- Development: Static provider (fast, debug symbols)
- Production: Dynamic provider (hot reload, updates)
- Embedded: Static provider only (no dependencies)

## Native Library Loading

    ModuleLoader loads dynamic libraries (.so/.dylib/.dll) using libloading
    crate with cross-platform support.

    **Implementation:** See `loader.rs::ModuleLoader`

**Given** path to dynamic library
        **When** loading library
        **Then** returns LoadedModule handle

        **Example:**
        ```simple
        val loader = ModuleLoader.new()
        val module = loader.load("path/to/library.so")
        ```

        **Platform Support:**
        - Linux: .so (ELF)
        - macOS: .dylib (Mach-O)
        - Windows: .dll (PE)

        **Verification:** Library loading works

**Given** loaded library
        **When** looking up symbol by name
        **Then** returns typed function pointer

        **Example:**
        ```simple
        val sqrt_fn = module.get_fn<fn(f64) -> f64>("sqrt")
        val result = sqrt_fn(42.0)  # Type-safe call
        ```

        **Symbol Resolution:**
        1. Convert name to C string
        2. dlsym lookup
        3. Cast to function pointer type
        4. Return typed pointer

        **Verification:** Symbol lookup works

**Given** invalid library path
        **When** attempting to load
        **Then** returns LoadError

        **Error Types:**
        - Io: File not found
        - Dl: dlopen failure (invalid library)
        - InvalidSymbolName: Bad symbol name

        **Example:**
        ```simple
        match loader.load("nonexistent.so"):
            Ok(module) => use_module(module)
            Err(LoadError.Io) => # File not found
        ```

        **Verification:** Error handling works

## Module Registry

    ModuleRegistry manages loaded modules with caching, lookup, and hot reload.

    **Implementation:** See `registry.rs::ModuleRegistry`

**Given** loaded module
        **When** inserting into registry
        **Then** stores for reuse

        **Example:**
        ```simple
        val registry = ModuleRegistry.new()
        val module = loader.load("math.so")
        registry.insert("math.so", module)

        # Later: reuse without reloading
        val cached = registry.get("math.so")
        ```

        **Benefits:**
        - Avoid redundant loading
        - Share across components
        - Hot reload support

        **Verification:** Module caching works

**Given** cached module
        **When** removing and reloading
        **Then** updates registry with new version

        **Hot Reload Steps:**
        ```simple
        # Remove old version
        registry.remove("plugin.so")

        # Load new version
        val new_module = loader.load("plugin.so")
        registry.insert("plugin.so", new_module)
        ```

        **Use Cases:**
        - Plugin updates
        - Development iteration
        - Runtime patching

        **Verification:** Hot reload works

## Runtime Symbol Providers

    Three-tier symbol resolution: static, dynamic, and chained providers.

    **Implementation:** See `provider.rs`, `static_provider.rs`, `dynamic_provider.rs`

**Given** static provider with linked symbols
        **When** looking up symbol
        **Then** returns compile-time linked pointer

        **Static Provider:**
        ```simple
        val provider = static_provider()
        val malloc = provider.lookup("malloc")  # Fast O(1) lookup
        ```

        **Advantages:**
        - Fast (direct pointer)
        - Always available
        - No runtime deps

        **Verification:** Static symbol resolution works

**Given** dynamic provider with runtime library
        **When** looking up symbol
        **Then** performs dlsym lookup

        **Dynamic Provider:**
        ```simple
        val provider = dynamic_provider("libruntime.so")
        val print = provider.lookup("print")  # Runtime lookup
        ```

        **Advantages:**
        - Flexible
        - Hot reload
        - Smaller binary

        **Verification:** Dynamic symbol resolution works

**Given** chained provider with multiple backends
        **When** looking up symbol
        **Then** tries providers in order

        **Chained Provider:**
        ```simple
        val provider = chained_provider([static, dynamic, fallback])
        val symbol = provider.lookup("custom_fn")
        # Tries: static → dynamic → fallback
        ```

        **Resolution Strategy:**
        First provider with symbol wins

        **Verification:** Provider chaining works

## ABI Compatibility Checking

    Ensures runtime and module use compatible ABIs.

    **Implementation:** See `simple_common::AbiVersion`

**Given** runtime and module versions
        **When** checking compatibility
        **Then** validates version constraints

        **Compatibility:**
        - Major: Must match
        - Minor: Backward compatible
        - Patch: Always compatible

        **Examples:**
        ```
        Runtime 1.2.3, Module 1.2.0 → Compatible
        Runtime 1.3.0, Module 1.2.5 → Compatible
        Runtime 1.2.0, Module 2.0.0 → Incompatible (major)
        Runtime 1.3.0, Module 1.4.0 → Incompatible (minor)
        ```

        **Verification:** ABI checking works

**Given** incompatible ABI versions
        **When** loading module
        **Then** returns compatibility error

        **Example:**
        ```simple
        val provider = dynamic_provider("libmodule.so")
        match provider.check_abi_version(2, 0, 0):
            Ok(_) => load_module()
            Err(IncompatibleAbi) => # Abort
        ```

        **Error Handling:**
        Prevents undefined behavior from ABI mismatches

        **Verification:** Incompatibility detection works
