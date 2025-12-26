# Semantic Duplication Analysis - Simple Compiler

Generated: 2025-12-15

## Executive Summary

This document identifies semantically similar code that could be merged or refactored to reduce duplication and improve maintainability.

## 1. Module Loaders (High Priority)

### Files:
- `src/loader/src/loader.rs` (ModuleLoader for SMF)
- `src/loader/src/module.rs` (LoadedModule for SMF)
- `src/native_loader/src/loader.rs` (ModuleLoader for native libs)
- `src/native_loader/src/module.rs` (LoadedModule for native libs)

### Duplication:
Both implement identical interfaces with different backends:
- `ModuleLoader::new()` - identical signature
- `load(&self, path: &Path)` - identical signature
- `load_with_resolver<F>(&self, path, resolver)` - identical signature
- Both implement `DynLoader` trait from `simple_common`

### LoadedModule Duplication:
- `get_function<F>(&self, name: &str) -> Option<F>` - identical signature
- `entry_point<F>(&self) -> Option<F>` - identical signature
- Both implement `DynModule` trait from `simple_common`

### Recommendation:
**KEEP SEPARATE** - These are intentionally parallel implementations:
- SMF loader: custom binary format with relocation
- Native loader: OS dynamic library wrapper
- Different internal representations (ExecutableMemory vs Library)
- Common interface via DynLoader/DynModule traits already provides abstraction

**Action:** No merge needed - this is good polymorphism via traits.

---

## 2. Error Types (Medium Priority)

### Files:
- `src/parser/src/error.rs` (ParseError)
- `src/compiler/src/error.rs` (CompilerError with error codes)
- `src/pkg/src/error.rs` (PkgError)
- `src/gpu/src/error.rs` (GpuError)

### Common Patterns:
All use `thiserror::Error` derive macro with similar patterns:
```rust
#[error("...: {0}")]
SomeVariant(String),

#[error("...")]
Io(#[from] std::io::Error),
```

### Differences:
- Parser: focused on syntax/tokens with Span tracking
- Compiler: rich diagnostics with error codes (E1xxx, E2xxx, E3xxx)
- Pkg: dependency/version/manifest errors
- GPU: device/buffer/kernel errors

### Recommendation:
**KEEP SEPARATE** - Domain-specific errors are appropriate:
- Each crate has distinct error scenarios
- Error codes in compiler are unique to that domain
- Span tracking in parser is syntax-specific
- Converting to a generic error type would lose clarity

**Action:** Consider shared diagnostic infrastructure instead (see next section).

---

## 3. Diagnostic Infrastructure (High Priority - MERGE CANDIDATE)

### Current State:
- `src/parser/src/diagnostic.rs` - Diagnostic struct with Severity/Span
- `src/compiler/src/error.rs` - Imports parser's Diagnostic
- Multiple crates import from parser just for diagnostics

### Issue:
Diagnostics are a cross-cutting concern but live in parser crate, creating unnecessary dependency.

### Recommendation:
**MERGE INTO COMMON** - Create `src/common/src/diagnostic.rs`:
```rust
// Move from parser to common
pub struct Diagnostic { ... }
pub enum Severity { ... }
pub struct Label { ... }
```

**Benefits:**
- Breaks circular dependency
- All crates can use diagnostics without depending on parser
- Parser, compiler, pkg, gpu can all emit diagnostics

**Migration:**
1. Create `src/common/src/diagnostic.rs`
2. Move Diagnostic, Severity, Label from parser
3. Update all imports: `simple_parser::Diagnostic` → `simple_common::Diagnostic`
4. Remove diagnostic.rs from parser (or re-export from common)

---

## 4. Module Resolution (Medium Priority)

### Files:
- `src/compiler/src/module_resolver.rs` - Path resolution for .spl files
- `src/compiler/src/pipeline/module_loader.rs` - Module loading in pipeline
- `src/dependency_tracker/src/resolution.rs` - Dependency resolution

### Overlap:
- All deal with module/import resolution
- All track dependencies
- All handle paths and __init__.spl

### Recommendation:
**CONSOLIDATE LOGIC** - Not a full merge, but extract shared utilities:

Create `src/common/src/module_path.rs`:
```rust
pub struct ModulePath { ... }
impl ModulePath {
    pub fn resolve(&self, base: &Path) -> PathBuf { ... }
    pub fn find_init(dir: &Path) -> Option<PathBuf> { ... }
}
```

**Benefits:**
- Shared path resolution logic
- Consistent __init__.spl handling
- Reduce test duplication

---

## 5. Value Conversion/Marshalling (Low Priority)

### Files:
- `src/compiler/src/value.rs` - Interpreter Value enum
- `src/compiler/src/value_bridge.rs` - FFI bridge values
- `src/runtime/src/value/core.rs` - RuntimeValue tagged pointer

### Current State:
These are intentionally different representations:
- Interpreter: boxed Rust types for flexibility
- Bridge: conversion layer
- Runtime: 64-bit tagged pointers for performance

### Recommendation:
**KEEP SEPARATE** - Different layers need different representations.

**Action:** Ensure conversion functions are well-tested and documented.

---

## 6. Memory Management Abstractions (Low Priority)

### Files:
- `src/runtime/src/memory/gc.rs` - GC wrapper
- `src/runtime/src/memory/gcless.rs` - GC-less wrapper
- `src/runtime/src/memory/no_gc.rs` - NoGC allocator
- `src/embedded/src/memory.rs` - Embedded memory management

### Overlap:
All provide memory allocation abstractions.

### Recommendation:
**KEEP SEPARATE** - Different execution environments:
- Runtime: general-purpose with GC options
- Embedded: constrained environments, no_std

**Action:** Consider trait-based abstraction if more allocators are added.

---

## 7. Test Helpers (High Priority - MERGE CANDIDATE)

### Pattern Found:
Many test files have similar helper functions:
```rust
fn run_expect(src: &str, expected: i32) { ... }
fn assert_compile_error(src: &str) { ... }
fn temp_file_with_content(content: &str) -> TempFile { ... }
```

### Recommendation:
**CREATE TEST UTILITIES CRATE** - `src/test_util/`:
```rust
// src/test_util/src/lib.rs
pub mod runner {
    pub fn run_expect(src: &str, expected: i32) { ... }
    pub fn run_async(src: &str) -> JoinHandle { ... }
}

pub mod files {
    pub fn temp_simple_file(name: &str, content: &str) -> TempFile { ... }
    pub fn temp_project(files: &[(&str, &str)]) -> TempDir { ... }
}

pub mod assertions {
    pub fn assert_compile_error(result: Result<...>) { ... }
    pub fn assert_runtime_error(result: Result<...>) { ... }
}
```

**Benefits:**
- Reduce test code duplication
- Consistent test patterns
- Easier to add new test utilities

---

## Summary of Recommendations

| Item | Action | Priority | Effort |
|------|--------|----------|--------|
| Module Loaders | Keep separate (good design) | N/A | None |
| Error Types | Keep separate (domain-specific) | N/A | None |
| Diagnostic Infrastructure | **Merge into common** | High | Small |
| Module Resolution Utils | Extract shared logic | Medium | Medium |
| Value Representations | Keep separate (layered) | N/A | None |
| Memory Abstractions | Keep separate (environment-specific) | N/A | None |
| Test Helpers | **Create test_util crate** | High | Medium |

## Next Steps

1. **Immediate (High Priority):**
   - Move diagnostics to `simple_common`
   - Create `simple_test_util` crate for test helpers

2. **Near-term (Medium Priority):**
   - Extract shared module path utilities
   - Review dependency_tracker vs module_resolver overlap

3. **Future (Low Priority):**
   - Document the intentional separation of loaders/values/memory
   - Add trait-based memory abstraction if needed
