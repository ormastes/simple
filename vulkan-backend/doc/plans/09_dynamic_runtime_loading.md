# Dynamic Runtime Library Loading

## Overview

This feature adds support for dynamically loading runtime FFI functions from shared libraries (.so/.dylib/.dll) as an alternative to static linking. The interpreter and compiler share a unified interface for symbol resolution.

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    RuntimeSymbolProvider trait                   │
│   fn get_symbol(&self, name: &str) -> Option<*const u8>         │
│   fn has_symbol(&self, name: &str) -> bool                      │
│   fn abi_version(&self) -> AbiVersion                           │
└─────────────────────────────────────────────────────────────────┘
                              │
     ┌────────────────────────┼────────────────────────┐
     ▼                        ▼                        ▼
┌─────────────────┐  ┌─────────────────┐  ┌─────────────────────┐
│ StaticProvider  │  │ DynamicProvider │  │  ChainedProvider    │
│ (compiled-in)   │  │ (loads .so/dll) │  │ (multiple libs)     │
│ - Zero cost     │  │ - libloading    │  │ - First-match wins  │
│ - Default       │  │ - Platform APIs │  │ - Plugin support    │
└─────────────────┘  └─────────────────┘  └─────────────────────┘
```

## Usage

### Static Linking (Default)

```rust
use simple_native_loader::static_provider;

// Zero-cost static linking (compiled into binary)
let provider = static_provider();
let ptr = provider.get_symbol("rt_array_new").unwrap();
```

### Dynamic Loading

```rust
use simple_native_loader::{DynamicSymbolProvider, RuntimeLoadMode, create_runtime_provider};

// Load from default system path
let provider = DynamicSymbolProvider::load_default()?;

// Load from specific path
let provider = DynamicSymbolProvider::load(Path::new("/path/to/libsimple_runtime.so"))?;

// Or use the factory
let provider = create_runtime_provider(RuntimeLoadMode::DynamicPath("/path/to/lib.so".into()))?;
```

### Chained Providers (Plugin Support)

```rust
use simple_native_loader::{ChainedProvider, StaticSymbolProvider, DynamicSymbolProvider};

let mut chain = ChainedProvider::new();

// Add plugin first (highest priority)
if let Ok(plugin) = DynamicSymbolProvider::load(Path::new("myplugin.so")) {
    chain.add(Arc::new(plugin));
}

// Fall back to static provider
chain.add(Arc::new(StaticSymbolProvider::default()));

// First provider with the symbol wins
let ptr = chain.get_symbol("rt_array_new");
```

### With JIT Compiler

```rust
use simple_compiler::codegen::JitCompiler;

// Default: uses static_provider() in release, tries dynamic in debug
let jit = JitCompiler::new()?;

// Custom provider
let jit = JitCompiler::with_provider(my_provider)?;

// Explicit static-only
let jit = JitCompiler::new_static()?;
```

## ABI Versioning

The runtime library exports an ABI version function:

```c
uint32_t simple_runtime_abi_version();  // Returns (major << 16) | minor
```

Version compatibility rules:
- **Major version**: Must match exactly (breaking changes)
- **Minor version**: Provider must be >= required (additive changes)

```rust
// Automatic version check on load
let provider = DynamicSymbolProvider::load(path)?; // Fails if ABI incompatible

// Manual check
if !provider.abi_version().is_compatible_with(&AbiVersion::CURRENT) {
    return Err("Incompatible runtime version");
}
```

### Version Bump Guidelines

| Change Type | Version Bump | Example |
|-------------|--------------|---------|
| Breaking: signature change | Major++ | `rt_array_new(i64)` → `rt_array_new(i64, i64)` |
| Breaking: remove symbol | Major++ | Remove `rt_legacy_fn` |
| Additive: new symbol | Minor++ | Add `rt_array_reverse` |
| Internal: same API | None | Refactor implementation |

## Platform Support

| Platform | Library Extension | Search Path | Build Output |
|----------|------------------|-------------|--------------|
| Linux | .so | LD_LIBRARY_PATH, /usr/lib | `libsimple_runtime.so` |
| macOS | .dylib | DYLD_LIBRARY_PATH, /usr/local/lib | `libsimple_runtime.dylib` |
| Windows | .dll | PATH, executable dir | `simple_runtime.dll` |

## Building the Shared Library

The runtime crate is configured to build both static (rlib) and dynamic (cdylib) libraries:

```bash
# Build release version (smaller, optimized)
cargo build -p simple-runtime --release

# Output: target/release/libsimple_runtime.so (Linux)
#         target/release/libsimple_runtime.dylib (macOS)
#         target/release/simple_runtime.dll (Windows)
```

## Performance Considerations

| Approach | First Lookup | Cached Lookup | Memory |
|----------|--------------|---------------|--------|
| Static | 0 | 0 | Linked into binary |
| Dynamic | ~1-10μs | 0 (cached) | Separate .so/.dll |
| Chained | Sum of providers | 0 (cached) | All loaded libs |

Recommendation:
- **Release builds**: Use `StaticSymbolProvider` (zero overhead)
- **Debug builds**: Use `ChainedProvider` with dynamic fallback (hot reload)
- **Plugins**: Use `ChainedProvider` with plugins first

## Files

| File | Description |
|------|-------------|
| `src/common/src/runtime_symbols.rs` | `RuntimeSymbolProvider` trait, `AbiVersion`, symbol list |
| `src/native_loader/src/static_provider.rs` | Static linking provider |
| `src/native_loader/src/dynamic_provider.rs` | Dynamic loading provider with ABI check |
| `src/native_loader/src/chained_provider.rs` | Multiple library support |
| `src/native_loader/src/provider.rs` | Factory and `RuntimeLoadMode` enum |
| `src/runtime/Cargo.toml` | Added `cdylib` crate-type |
| `src/runtime/src/lib.rs` | Exports `simple_runtime_abi_version()` |

## Symbol List

The following runtime FFI symbols are available (50+):

**Collections**: `rt_array_*`, `rt_tuple_*`, `rt_dict_*`, `rt_string_*`
**Values**: `rt_value_*`, `rt_index_*`, `rt_slice`, `rt_contains`
**Objects**: `rt_object_*`, `rt_closure_*`, `rt_enum_*`
**Memory**: `rt_alloc`, `rt_free`, `rt_ptr_to_value`, `rt_value_to_ptr`
**Async**: `rt_wait`, `rt_future_*`, `rt_actor_*`, `rt_generator_*`
**I/O**: `rt_print_*`, `rt_println_*`, `rt_eprint_*`, `rt_eprintln_*`
**Bridge**: `rt_interp_call`, `rt_interp_eval`, `rt_function_not_found`

See `RUNTIME_SYMBOL_NAMES` in `src/common/src/runtime_symbols.rs` for the full list.
